package marketplace

import (
	"errors"
	"fmt"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
)

// Work management for a freelance marketplace (in-memory, concurrency-safe).
// Intended as a starting point for persistence/HTTP adapters.

type ID string

func newID(prefix string, v uint64) ID { return ID(prefix + strconv.FormatUint(v, 10)) }

var idCounter uint64

// Entities

type User struct {
	ID    ID
	Name  string
	Email string
}

type Freelancer struct {
	User
	RatePerHour float64
	Skills      []string
}

type Client struct {
	User
}

type availabilityStatus string

const (
	Available   availabilityStatus = "available"
	Unavailable availabilityStatus = "unavailable"
	Offline      availabilityStatus = "offline"
	Busy         availabilityStatus = "busy"
)

type TaskStatus string

const (
	TaskOpen     TaskStatus = "open"
	TaskInProgress TaskStatus = "in_progress"
	TaskCompleted  TaskStatus = "completed"
)

type ProjectStatus string

const (
	ProjectOpen     ProjectStatus = "open"
	ProjectAssigned ProjectStatus = "assigned"
	ProjectClosed   ProjectStatus = "closed"
)

type Project struct {
	ID          ID
	ClientID    ID
	Title       string
	Description string
	Budget      float64
	Status      ProjectStatus
	CreatedAt   time.Time
}

type ProposalStatus string

const (
	ProposalPending  ProposalStatus = "pending"
	ProposalAccepted ProposalStatus = "accepted"
	ProposalRejected ProposalStatus = "rejected"
)

type Proposal struct {
	ID           ID
	ProjectID    ID
	FreelancerID ID
	Rate         float64
	EstimatedHrs float64
	Message      string
	Status       ProposalStatus
	SubmittedAt  time.Time
}

type ContractStatus string

const (
	ContractActive    ContractStatus = "active"
	ContractCompleted ContractStatus = "completed"
	ContractCancelled ContractStatus = "cancelled"
)

type Contract struct {
	ID           ID
	ProjectID    ID
	ProposalID   ID
	FreelancerID ID
	ClientID     ID
	StartAt      time.Time
	EndAt        *time.Time
	HourlyRate   float64
	AgreedHours  float64
	Status       ContractStatus

	// Aggregates maintained via WorkLog and Payments
	LoggedHours float64
	TotalPaid   float64
}

type WorkLog struct {
	ID           ID
	ContractID   ID
	FreelancerID ID
	Hours        float64
	Description  string
	CreatedAt    time.Time
}

type Payment struct {
	ID         ID
	ContractID ID
	Amount     float64
	PaidAt     time.Time
}

// WorkManager holds in-memory state. Use persistence for production.
type WorkManager struct {
	mu sync.RWMutex

	freelancers map[ID]*Freelancer
	clients     map[ID]*Client
	projects    map[ID]*Project
	proposals   map[ID]*Proposal
	contracts   map[ID]*Contract
	worklogs    map[ID]*WorkLog
	payments    map[ID]*Payment
}

// NewWorkManager creates an empty manager.
func NewWorkManager() *WorkManager {
	return &WorkManager{
		freelancers: make(map[ID]*Freelancer),
		clients:     make(map[ID]*Client),
		projects:    make(map[ID]*Project),
		proposals:   make(map[ID]*Proposal),
		contracts:   make(map[ID]*Contract),
		worklogs:    make(map[ID]*WorkLog),
		payments:    make(map[ID]*Payment),
	}
}

// RegisterFreelancer adds a freelancer.
func (m *WorkManager) RegisterFreelancer(name, email string, rate float64, skills []string) *Freelancer {
	uid := newID("f_", atomic.AddUint64(&idCounter, 1))
	f := &Freelancer{
		User:        User{ID: uid, Name: name, Email: email},
		RatePerHour: rate,
		Skills:      append([]string{}, skills...),
	}
	m.mu.Lock()
	m.freelancers[uid] = f
	m.mu.Unlock()
	return f
}

// RegisterClient adds a client.
func (m *WorkManager) RegisterClient(name, email string) *Client {
	uid := newID("c_", atomic.AddUint64(&idCounter, 1))
	c := &Client{User: User{ID: uid, Name: name, Email: email}}
	m.mu.Lock()
	m.clients[uid] = c
	m.mu.Unlock()
	return c
}

// CreateProject creates a new project for a client.
func (m *WorkManager) CreateProject(clientID ID, title, desc string, budget float64) (*Project, error) {
	m.mu.RLock()
	_, ok := m.clients[clientID]
	m.mu.RUnlock()
	if !ok {
		return nil, errors.New("client not found")
	}
	pid := newID("p_", atomic.AddUint64(&idCounter, 1))
	pr := &Project{
		ID:          pid,
		ClientID:    clientID,
		Title:       title,
		Description: desc,
		Budget:      budget,
		Status:      ProjectOpen,
		CreatedAt:   time.Now(),
	}
	m.mu.Lock()
	m.projects[pid] = pr
	m.mu.Unlock()
	return pr, nil
}

// SubmitProposal lets a freelancer propose for a project.
func (m *WorkManager) SubmitProposal(projectID, freelancerID ID, rate, estHrs float64, message string) (*Proposal, error) {
	m.mu.RLock()
	_, okP := m.projects[projectID]
	_, okF := m.freelancers[freelancerID]
	m.mu.RUnlock()
	if !okP {
		return nil, errors.New("project not found")
	}
	if !okF {
		return nil, errors.New("freelancer not found")
	}
	pid := newID("pr_", atomic.AddUint64(&idCounter, 1))
	prop := &Proposal{
		ID:           pid,
		ProjectID:    projectID,
		FreelancerID: freelancerID,
		Rate:         rate,
		EstimatedHrs: estHrs,
		Message:      message,
		Status:       ProposalPending,
		SubmittedAt:  time.Now(),
	}
	m.mu.Lock()
	m.proposals[pid] = prop
	m.mu.Unlock()
	return prop, nil
}

// AcceptProposal converts a proposal into a contract. Only the project owner (clientID) may accept.
func (m *WorkManager) AcceptProposal(proposalID, clientID ID) (*Contract, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	prop, ok := m.proposals[proposalID]
	if !ok {
		return nil, errors.New("proposal not found")
	}
	if prop.Status != ProposalPending {
		return nil, errors.New("proposal is not pending")
	}
	project, ok := m.projects[prop.ProjectID]
	if !ok {
		return nil, errors.New("project not found")
	}
	if project.ClientID != clientID {
		return nil, errors.New("only project owner can accept proposals")
	}
	// Mark proposal accepted, update project status
	prop.Status = ProposalAccepted
	project.Status = ProjectAssigned

	cid := newID("ct_", atomic.AddUint64(&idCounter, 1))
	contract := &Contract{
		ID:           cid,
		ProjectID:    project.ID,
		ProposalID:   prop.ID,
		FreelancerID: prop.FreelancerID,
		ClientID:     clientID,
		StartAt:      time.Now(),
		HourlyRate:   prop.Rate,
		AgreedHours:  prop.EstimatedHrs,
		Status:       ContractActive,
	}
	m.contracts[cid] = contract
	return contract, nil
}

// LogWork records hours worked by freelancer under a contract.
func (m *WorkManager) LogWork(contractID, freelancerID ID, hours float64, description string) (*WorkLog, error) {
	if hours <= 0 {
		return nil, errors.New("hours must be positive")
	}

	m.mu.Lock()
	defer m.mu.Unlock()

	contract, ok := m.contracts[contractID]
	if !ok {
		return nil, errors.New("contract not found")
	}
	if contract.Status != ContractActive {
		return nil, errors.New("contract is not active")
	}
	if contract.FreelancerID != freelancerID {
		return nil, errors.New("freelancer not assigned to contract")
	}

	wid := newID("w_", atomic.AddUint64(&idCounter, 1))
	log := &WorkLog{
		ID:           wid,
		ContractID:   contractID,
		FreelancerID: freelancerID,
		Hours:        hours,
		Description:  description,
		CreatedAt:    time.Now(),
	}
	m.worklogs[wid] = log
	contract.LoggedHours += hours
	return log, nil
}

// CreateInvoice computes outstanding amount for a contract.
func (m *WorkManager) CreateInvoice(contractID ID) (totalDue float64, totalLogged float64, totalPaid float64, err error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	contract, ok := m.contracts[contractID]
	if !ok {
		return 0, 0, 0, errors.New("contract not found")
	}
	totalLogged = contract.LoggedHours
	totalPaid = contract.TotalPaid
	totalDue = totalLogged*contract.HourlyRate - totalPaid
	if totalDue < 0 {
		totalDue = 0
	}
	return totalDue, totalLogged, totalPaid, nil
}

// Pay records a payment against a contract. Returns the payment record.
func (m *WorkManager) Pay(contractID ID, amount float64) (*Payment, error) {
	if amount <= 0 {
		return nil, errors.New("amount must be positive")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	contract, ok := m.contracts[contractID]
	if !ok {
		return nil, errors.New("contract not found")
	}
	pid := newID("pay_", atomic.AddUint64(&idCounter, 1))
	p := &Payment{
		ID:         pid,
		ContractID: contractID,
		Amount:     amount,
		PaidAt:     time.Now(),
	}
	m.payments[pid] = p
	contract.TotalPaid += amount

	// Optionally close contract if fully paid and hours met.
	if contract.TotalPaid >= contract.LoggedHours*contract.HourlyRate && contract.LoggedHours >= contract.AgreedHours {
		contract.Status = ContractCompleted
		now := time.Now()
		contract.EndAt = &now
	}
	return p, nil
}

// GetContract returns a copy of contract or error.
func (m *WorkManager) GetContract(contractID ID) (*Contract, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	c, ok := m.contracts[contractID]
	if !ok {
		return nil, errors.New("contract not found")
	}
	// return a copy to prevent external mutation
	copy := *c
	return &copy, nil
}

// Basic listing functions

func (m *WorkManager) ListOpenProjects() []*Project {
	m.mu.RLock()
	defer m.mu.RUnlock()
	out := make([]*Project, 0, len(m.projects))
	for _, p := range m.projects {
		if p.Status == ProjectOpen {
			// shallow copy
			cp := *p
			out = append(out, &cp)
		}
	}
	return out
}

func (m *WorkManager) ListProposalsForProject(projectID ID) []*Proposal {
	m.mu.RLock()
	defer m.mu.RUnlock()
	out := make([]*Proposal, 0)
	for _, pr := range m.proposals {
		if pr.ProjectID == projectID {
			cp := *pr
			out = append(out, &cp)
		}
	}
	return out
}

func (m *WorkManager) ListContractsForFreelancer(freelancerID ID) []*Contract {
	m.mu.RLock()
	defer m.mu.RUnlock()
	out := make([]*Contract, 0)
	for _, c := range m.contracts {
		if c.FreelancerID == freelancerID {
			cp := *c
			out = append(out, &cp)
		}
	}
	return out
}

// Helpers for debugging/summary

func (m *WorkManager) ContractSummary(contractID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	c, ok := m.contracts[contractID]
	if !ok {
		return "", errors.New("contract not found")
	}
	totalOwed := c.LoggedHours*c.HourlyRate - c.TotalPaid
	if totalOwed < 0 {
		totalOwed = 0
	}
	return fmt.Sprintf("Contract %s: status=%s freelancer=%s client=%s logged=%.2fhrs rate=%.2f total_paid=%.2f owed=%.2f",
		c.ID, c.Status, c.FreelancerID, c.ClientID, c.LoggedHours, c.HourlyRate, c.TotalPaid, totalOwed), nil
}

func (m *WorkManager) FreelancerSummary(freelancerID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	f, ok := m.freelancers[freelancerID]
	if !ok {
		return "", errors.New("freelancer not found")
	}
	totalContracts := 0
	totalLogged := 0.0
	totalPaid := 0.0
	for _, c := range m.contracts {
		if c.FreelancerID == freelancerID {
			totalContracts++
			totalLogged += c.LoggedHours
			totalPaid += c.TotalPaid
		}
	}
	return fmt.Sprintf("Freelancer %s: rate=%.2f skills=%v contracts=%d total_logged=%.2fhrs total_paid=%.2f",
		f.Name, f.RatePerHour, f.Skills, totalContracts, totalLogged, totalPaid), nil
}

func (m *WorkManager) ClientSummary(clientID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	c, ok := m.clients[clientID]
	if !ok {
		return "", errors.New("client not found")
	}
	totalProjects := 0
	totalContracts := 0
	totalPaid := 0.0
	for _, p := range m.projects {
		if p.ClientID == clientID {
			totalProjects++
		}
	}
	for _, c := range m.contracts {
		if c.ClientID == clientID {
			totalContracts++
			totalPaid += c.TotalPaid
		}
	}
	totalOwed := 0.0
	for _, c := range m.contracts {
		if c.ClientID == clientID {
			owed := c.LoggedHours*c.HourlyRate - c.TotalPaid
			if owed > 0 {
				totalOwed += owed
			}
		}
	}
	if totalOwed < 0 {
		totalOwed = 0
	}
	return fmt.Sprintf("Client %s: projects=%d contracts=%d total_paid=%.2f total_owed=%.2f",
		c.Name, totalProjects, totalContracts, totalPaid, totalOwed), nil
}

func (m *WorkManager) ProjectSummary(projectID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	p, ok := m.projects[projectID]
	if !ok {
		return "", errors.New("project not found")
	}
	totalProposals := 0
	for _, pr := range m.proposals {
		if pr.ProjectID == projectID {
			totalProposals++
		}
	}
	return fmt.Sprintf("Project %s: title=%s status=%s budget=%.2f proposals=%d",
		p.ID, p.Title, p.Status, p.Budget, totalProposals), nil
}

func (m *WorkManager) ProposalSummary(proposalID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	pr, ok := m.proposals[proposalID]
	if !ok {
		return "", errors.New("proposal not found")
	}
	return fmt.Sprintf("Proposal %s: project=%s freelancer=%s rate=%.2f est_hrs=%.2f status=%s",
		pr.ID, pr.ProjectID, pr.FreelancerID, pr.Rate, pr.EstimatedHrs, pr.Status), nil
}

func (m *WorkManager) WorkLogSummary(workLogID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	wl, ok := m.worklogs[workLogID]
	if !ok {
		return "", errors.New("work log not found")
	}
	return fmt.Sprintf("WorkLog %s: contract=%s freelancer=%s hours=%.2f desc=%s",
		wl.ID, wl.ContractID, wl.FreelancerID, wl.Hours, wl.Description), nil
}

func (m *WorkManager) PaymentSummary(paymentID ID) (string, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	p, ok := m.payments[paymentID]
	if !ok {
		return "", errors.New("payment not found")
	}
	return fmt.Sprintf("Payment %s: contract=%s amount=%.2f paid_at=%s",
		p.ID, p.ContractID, p.Amount, p.PaidAt.Format(time.RFC3339)), nil
}

func RegisterFreelancer(name, email string, rate float64, skills []string) *Freelancer {
	manager := NewWorkManager()
	return manager.RegisterFreelancer(name, email, rate, skills)
}

func removeFreelancer(manager *WorkManager, freelancerID ID) error {
	manager.mu.Lock()
	defer manager.mu.Unlock()
	if _, ok := manager.freelancers[freelancerID]; !ok {
		return errors.New("freelancer not found")
	}
	delete(manager.freelancers, freelancerID)
	return nil
}

func RegisterClient(name, email string) *Client {
	manager := NewWorkManager()
	return manager.RegisterClient(name, email)
}

func CreateProject(clientID ID, title, desc string, budget float64) (*Project, error) {
	manager := NewWorkManager()
	return manager.CreateProject(clientID, title, desc, budget)
}

func updateAvailability(manager *WorkManager, freelancerID ID, available bool) error {
	manager.mu.Lock()
	defer manager.mu.Unlock()
	freelancer, ok := manager.freelancers[freelancerID]
	if !ok {
		return errors.New("freelancer not found")
	}
	_ = freelancer // Placeholder for actual availability update logic
	return nil
}

func updateRate(manager *WorkManager, freelancerID ID, newRate float64) error {
	manager.mu.Lock()
	defer manager.mu.Unlock()
	freelancer, ok := manager.freelancers[freelancerID]
	if !ok {
		return errors.New("freelancer not found")
	}
	freelancer.RatePerHour = newRate
	return nil
}

func updateSkills(manager *WorkManager, freelancerID ID, newSkills []string) error {
	manager.mu.Lock()
	defer manager.mu.Unlock()
	freelancer, ok := manager.freelancers[freelancerID]
	if !ok {
		return errors.New("freelancer not found")
	}
	freelancer.Skills = append([]string{}, newSkills...)
	return nil
}

func getPaymentsForFreelancer(manager *WorkManager, freelancerID ID) ([]*Payment, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.freelancers[freelancerID]
	if !ok {
		return nil, errors.New("freelancer not found")
	}
	var payments []*Payment
	for _, payment := range manager.payments {
		contract, ok := manager.contracts[payment.ContractID]
		if ok && contract.FreelancerID == freelancerID {
			payments = append(payments, payment)
		}
	}
	return payments, nil
}

FUNC totalPaidToFreelancer(manager *WorkManager, freelancerID ID) (float64, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.freelancers[freelancerID]
	if !ok {
		return 0, errors.New("freelancer not found")
	}
	var total float64
	for _, payment := range manager.payments {
		contract, ok := manager.contracts[payment.ContractID]
		if ok && contract.FreelancerID == freelancerID {
			total += payment.Amount
		}
	}
	return total, nil
}

func suggestFreelancersForTask(manager *WorkManager, requiredSkills []string) ([]*Freelancer, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	var suggestions []*Freelancer
skillLoop:
	for _, freelancer := range manager.freelancers {
		for _, reqSkill := range requiredSkills {
			skillFound := false
			for _, fSkill := range freelancer.Skills {
				if fSkill == reqSkill {
					skillFound = true
					break
				}
			if !skillFound {
				continue skillLoop
			}
		}
		suggestions = append(suggestions, freelancer)
	}
	return suggestions, nil
}

func getActiveContractsForClient(manager *WorkManager, clientID ID) ([]*Contract, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.clients[clientID]
	if !ok {
		return nil, errors.New("client not found")
	}
	var activeContracts []*Contract
	for _, contract := range manager.contracts {
		if contract.ClientID == clientID && contract.Status == ContractActive {
			activeContracts = append(activeContracts, contract)
		}
	}
	return activeContracts, nil
}

func getWorkLogsForContract(manager *WorkManager, contractID ID) ([]*WorkLog, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.contracts[contractID]
	if !ok {
		return nil, errors.New("contract not found")
	}
	var workLogs []*WorkLog
	for _, log := range manager.worklogs {
		if log.ContractID == contractID {
			workLogs = append(workLogs, log)
		}
	}
	return workLogs, nil
}

func getProposalsByFreelancer(manager *WorkManager, freelancerID ID) ([]*Proposal, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.freelancers[freelancerID]
	if !ok {
		return nil, errors.New("freelancer not found")
	}
	var proposals []*Proposal
	for _, proposal := range manager.proposals {
		if proposal.FreelancerID == freelancerID {	
			proposals = append(proposals, proposal)
		}
	}
	return proposals, nil
}

func getProjectsByClient(manager *WorkManager, clientID ID) ([]*Project, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.clients[clientID]
	if !ok {
		return nil, errors.New("client not found")
	}
	var projects []*Project
	for _, project := range manager.projects {
		if project.ClientID == clientID {
			projects = append(projects, project)
		}
	}
	return projects, nil
}

func getTotalLoggedHoursForFreelancer(manager *WorkManager, freelancerID ID) (float64, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.freelancers[freelancerID]
	if !ok {
		return 0, errors.New("freelancer not found")
	}
	var totalHours float64
	for _, log := range manager.worklogs {
		if log.FreelancerID == freelancerID {
			totalHours += log.Hours
		}
	}
	return totalHours, nil
}

func getTotalEarningsForFreelancer(manager *WorkManager, freelancerID ID) (float64, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.freelancers[freelancerID]
	if !ok {
		return 0, errors.New("freelancer not found")
	}
	var totalEarnings float64
	for _, contract := range manager.contracts {
		if contract.FreelancerID == freelancerID {
			totalEarnings += contract.TotalPaid
		}
	}
	return totalEarnings, nil
}

func getTotalSpentByClient(manager *WorkManager, clientID ID) (float64, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	_, ok := manager.clients[clientID]
	if !ok {
		return 0, errors.New("client not found")
	}
	var totalSpent float64
	for _, contract := range manager.contracts {
		if contract.ClientID == clientID {
			totalSpent += contract.TotalPaid
		}
	}
	return totalSpent, nil
}

func findFreelancersBySkill(manager *WorkManager, skill string) ([]*Freelancer, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	var freelancers []*Freelancer
	for _, freelancer := range manager.freelancers {
		for _, fSkill := range freelancer.Skills {
			if fSkill == skill {
				freelancers = append(freelancers, freelancer)
				break
			}
		}
	}
	return freelancers, nil
}

func findProjectsByKeyword(manager *WorkManager, keyword string) ([]*Project, error) {
	manager.mu.RLock()
	defer manager.mu.RUnlock()
	var projects []*Project
	for _, project := range manager.projects {
		if containsIgnoreCase(project.Title, keyword) || containsIgnoreCase(project.Description, keyword) {
			projects = append(projects, project)
		}
	}
	return projects, nil
}

func containsIgnoreCase(text, substr string) bool {
	textLower := strings.ToLower(text)
	substrLower := strings.ToLower(substr)
	return strings.Contains(textLower, substrLower)
}
