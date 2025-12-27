/** 
 * @File       : Ndarray.h
 * @Author     : eatondo
 * @Description: Datastructure for containing N dimensional
 *               arrays. 
 * @see : https://github.com/sheljohn/ndArray
 */

#ifndef _NDARRAY_H
#define _NDARRAY_H

// std library 
#include <iostream>
#include <cstdlib>
#include <cstdarg>
#include <cstdio>

#include <exception>
#include <stdexcept>

#include <memory>
#include <algorithm>
#include <type_traits>
#include <initializer_list>


namespace utilityLib {
// Comment for (slightly) faster access
#define ND_ARRAY_SAFE_ACCESS

// Protect 1D access
#ifdef ND_ARRAY_SAFE_ACCESS
    #define ND_ARRAY_PROTECT(k,n) (k % n)
#else
    #define ND_ARRAY_PROTECT(k,n) k
#endif


    using dimen_t   = uint8_t;          // dimension
    using index_t   = uint64_t;         // specific values of dimension
	using index_ptr = const index_t*;   // ptr to specific value in dimension


    /** 
     *
     */
	template <dimen_t N>
	index_t sub2ind( index_ptr dims, index_ptr size, index_ptr strides ) {
		index_t ind = 0;

		for (dimen_t i = 0; i < N; ++i)
			ind += ND_ARRAY_PROTECT(dims[i], size[i]) * strides[i];

		return ind;
	}

    /** 
     * 
     */
    template <dimen_t N>
	index_t sub2ind(va_list& vl, index_ptr size, index_ptr strides) {
		index_t ind = 0;

		// for (dimen_t i = 1; i < N; ++i)
		// 	ind += ND_ARRAY_PROTECT(va_arg(vl,index_t),size[i]) * strides[i];

		// va_end(vl); 
        return ind;
	}

    // template <> inline index_t
	// sub2ind<0>( index_ptr, index_ptr, index_ptr )
	// 	{ return 0; }
	// template <> inline index_t
	// sub2ind<1>( index_ptr subs, index_ptr size, index_ptr strides )
	// 	{ return
	// 		ND_ARRAY_PROTECT(subs[0],size[0])*strides[0]; }
	// template <> inline index_t
	// sub2ind<2>( index_ptr subs, index_ptr size, index_ptr strides )
	// 	{ return
	// 		ND_ARRAY_PROTECT(subs[0],size[0])*strides[0] +
	// 		ND_ARRAY_PROTECT(subs[1],size[1])*strides[1]; }
	// template <> inline index_t
	// sub2ind<3>( index_ptr subs, index_ptr size, index_ptr strides )
	// 	{ return
	// 		ND_ARRAY_PROTECT(subs[0],size[0])*strides[0] +
	// 		ND_ARRAY_PROTECT(subs[1],size[1])*strides[1] +
	// 		ND_ARRAY_PROTECT(subs[2],size[2])*strides[2]; }


    /**
	 * @brief   Dummy deleter functor.
	 *          performs no function
	 */
	template <typename T>
	struct no_delete { inline void operator() ( T* ptr ) const {} };


    /** 
     * @brief
     * @param   N   datatype of nd array 
     * @param   N   number of dimensions
     */
    template <typename T, unsigned N>
    class Ndarray {
    public:
        /* TYPE DEFINITIONS  */
        typedef T value_type;
        typedef T* pointer;
        typedef T& reference;

        typedef typename std::add_const<T>::type const_value;
        typedef const_value* const_pointer;
        typedef const_value& const_reference;

        typedef std::shared_ptr<value_type> shared;
        typedef Ndarray<T,N> self;


        /* Constructor(s) */
        Ndarray() {reset();}

        /* Initialization of Blank Array */
        /** 
         * @brief   allocate new ND array as a 1D array, with initializer list 
         * @param   dims    list of initial n dimension sizes
         */
        Ndarray(std::initializer_list<T> dims);

        /** 
         * @brief   allocate new ND array as a 1D array, with variadic dimension arguments
         * @param   dim    size of dimension
         * @param   ...    size of each dimensions of ND array 
         */
        // Ndarray(T dim...);

        /** 
         * @brief   allocate new ND array as a 1D array, with array specifying 
         *          size of nd array dimensions
         * @param   size    size of each dimension in array 
         */
        Ndarray(T (&a)[N]);

        /** 
         * @brief   allocate new ND array as a 1D array 
         * @param   ptr     new array that has size of total number of elements
         * @param   size    size of each dimension in array 
         * @param   manage  array data handling 
         */
        Ndarray(pointer ptr, index_ptr size, bool manage);

        /* Initialization with Pre-defined Array */
        /** 
         * @brief   create new ND array from 1D array, with intializer list 
         * @param   dims    list of initial n dimension sizes
         * @param   array   
         */
        Ndarray(std::initializer_list<T> dims, T* array);

        /** 
         * @brief   create new ND array from 1D array, with array 
         * @param   dims    list of initial n dimension sizes
         * @param   array   
         */
        Ndarray(int (&dims)[N], T* array, int numel);


        /** 
         * @brief   provide info about nd array  
         */
        void info();

         /** 
         * @brief   copy constructor
         * @param   other     object to be copied 
         */
        Ndarray(const self& other) { operator=(other); }
        self& operator= ( const self& other );

        
        /* ACCESS */
        // Direct data access
        inline const_pointer cdata() const { return m_data.get(); }
        inline pointer data() const { return m_data.get(); }

        // Iterators 
        inline const_pointer cbegin() const { return data(); }
        inline const_pointer cend() const { return data() + m_numel; }

        inline pointer begin() const { return data(); }
        inline pointer end() const { return data() + m_numel; }


        /* OPERATIONS */
        // Check pointer validity
		inline bool empty() const { return !((bool) m_data); }
		inline operator bool() const { return m_data; }
        
        /**
         *  @brief
         */
        void clear();

        /**
         *  @brief
         */
        void reset();

        /** 
         *  @brief   
         *  @param   ptr 
         *  @param   size
         *  @param   manage
         */
        // void assign(pointer ptr, index_ptr size, bool manage);
        // void assign(index_ptr size, bool manage);
        void assign(std::initializer_list<T> dims, bool manage);

        /** 
         *  @brief  swap contents with another array 
         */
        void swap();

        /** 
         *  @brief  copy contents U from other array to current array 
         *  @param  other   other array to be copied to current array
         */
        template<typename U>
        void copy(const Ndarray<U,N>& other);

        /* Operators */
        /**     
         *  @brief  Copy matrix 
         * 
         */
        self& operator&(const self& other) {
            return 0;
        };

        /** 
         *  @brief  Access single dimension 
         */
        inline reference operator[] (index_t n) const {
            return data()[ ND_ARRAY_PROTECT(n,m_numel) ];
        } 

        /** 
         *  @brief  Access N dimensions via intializer list 
         */
        inline reference operator() (std::initializer_list<T> dims) const {
            return data()[ sub2ind<N>(dims, m_size, m_strides) ]; 
        }

        /** 
         *  @brief  Access N dimensions via coordinates
         */
		reference operator() ( index_t i, ... ) const {
            va_list vl; 
            va_start(vl,i);
            return data()[ (i*m_strides[0]) + sub2ind<N>(vl, m_size, m_strides) ];
        }

        /** 
         *  @brief  Convert 1D array to ND array 
         *  @param  array   1D array to convert 
         */
        Ndarray toArrayND(T* array);

        /** 
         *  @brief  Convert 1D array to ND array 
         *  @param  array   1D array to convert 
         */
        std::string toString(T* array);


    protected:
        /** */
        void assign_shared(pointer ptr, bool manage );

        /** */
        void shallowCopy();

        /** */
        void deepCopy();

        /* Internal array data */
        index_t m_numel;       // total number of array elements 
        index_t m_size[N];     // size of each dimension 
        index_t m_strides[N];  // stride of dimensions (start value of each dimension in 1D array)
        shared  m_data;        // internal array values
    };


    // Include implementation 
    #include "Ndarray.hpp"
}

#endif // _NDARRAY_H