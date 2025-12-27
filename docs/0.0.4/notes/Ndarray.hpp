/** 
 * @File       : Ndarray.hpp
 * @Author     : eatondo
 * @Description: Implementation of Ndarray functions 
 */


/* Initialization of Blank Array */

template <typename T, unsigned N>
Ndarray<T,N>::Ndarray(std::initializer_list<T> dims) {
	bool manage = true; 
	assign(dims, manage);
}

template <typename T, unsigned N>
Ndarray<T,N>::Ndarray(T (&dims)[N]) {
	index_t numel = 1;
	bool manage = true;
	// const index_ptr ss[2] = {3, 4};
	for (int i=0; i<N; i++) numel *= dims[i];
	std::cout << numel << std::endl;
	std::cout << N << std::endl;
	// std::cout << (int)((char *)(&size+1) - (char *)(&size)) << std::endl; 
	// assign(new short[numel], ss, true);

	// assign(new T [numel], numel, manage);
}

template <typename T, unsigned N>
Ndarray<T, N>::Ndarray(pointer ptr, index_ptr size, bool manage) {
	// assign(ptr, size, manage);
}


/* Initialization with Pre-defined Array */

template <typename T, unsigned N>
Ndarray<T,N>::Ndarray(std::initializer_list<T> dims, T* array) {
	// for (int i=0; i<N; i++) std::cout << dims[i] << '\n';
	// for (auto i: dims) std::cout << i << '\n';
	// for (auto i: array) std::cout << i << '\n';
}

template <typename T, unsigned N>
Ndarray<T,N>::Ndarray(int (&dims)[N], T* array, int numel) {
	// index_t numel = 1;
	// for (int i=0; i<N; i++) numel *= dims[i];
	// for (int i=0; i<N; i++) std::cout << dims[i] << '\n';
	// for (int i=0; i<numel; i++) std::cout << array[i] << '\n';
	// for (auto i: dims) std::cout << i << '\n';
	// for (auto i: array) std::cout << i << '\n';
}


/* OPERATIONS */

template <typename T, unsigned N>
void Ndarray<T,N>::clear() {
	m_data.reset();
}

template <typename T, unsigned N>
void Ndarray<T,N>::reset() {
    clear();
	m_numel = 0;

}


/* Operators */

template <typename T, unsigned N>
Ndarray<T,N> Ndarray<T,N>::toArrayND(T* array) {

}

template <typename T, unsigned N>
std::string Ndarray<T,N>::toString(T* array) {

}


template <typename T, unsigned N>
// void Ndarray<T,N>::assign(pointer ptr, index_ptr size, bool manage)
// void Ndarray<T,N>::assign(index_ptr size, bool manage) {
void Ndarray<T, N>::assign(std::initializer_list<T> dims, bool manage) {
	m_numel = 1;	
	int i = 0;
	for (auto d: dims) {
		m_size[i] = d;
		m_numel *= d;
		m_strides[(i+1) % N] = m_numel;
		// std::cout << "m_size	" << m_size[i] << std::endl;
		// std::cout << "m_numel	" << m_numel << std::endl;
		// std::cout << "m_strides	" << m_strides[(i+1) % N] << std::endl;
		++i;
	}
        
	T* ptr = new T[m_numel];
	m_strides[0] = 1;
	
	// set internal data
	assign_shared(ptr, manage);
}

template <typename T, unsigned N>
void Ndarray<T,N>::assign_shared(pointer ptr, bool manage)
{
	if (manage)
		m_data.reset(ptr);
	else
		m_data.reset( ptr, no_delete<T>() );
}

template <typename T, unsigned N>
void Ndarray<T,N>::info() {
	std::cout << "array info" << std::endl; 
}

