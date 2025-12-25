const ws = new WebSocket("ws://localhost:8080/ws");

ws.onmessage = (ev) => {
    const msg = JSON.parse(ev.data);

    // update job list
    const div = document.getElementById("jobs");
    div.innerHTML = "";
    msg.jobs.forEach(job => {
        const btn = `<button onclick="trigger(${job.id})">Run</button>`;
        div.innerHTML += `<div>${job.name} - ${job.status} ${btn}</div>`;
    });

    // update logs if selected
    if (msg.selectedLog) {
        document.getElementById("log").textContent = msg.selectedLog;
    }
};

function trigger(id) {
    ws.send(JSON.stringify({ trigger: id }));
}

function viewLog(id) {
    ws.send(JSON.stringify({ log: id }));
}
