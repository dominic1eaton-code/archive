/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

struct Vector
{
    /* */
    float x,
          y;

    /* */
    inline Vector operator+(float scale) const;

    /* */
    inline Vector operator-(float scale) const;

    /* */
    inline Vector operator*(float scale) const;

    /* */
    inline Vector operator/(float scale) const;

    /* */
    inline Vector operator+(const Vector& V) const;

    /* */
    inline Vector operator-(const Vector& V) const;

    /* */
    inline Vector operator*(const Vector& V) const;

    /* */
    inline Vector operator/(const Vector& V) const;

    /* */
    inline Vector operator==(const Vector& V) const;

    /* */
    inline Vector operator!=(const Vector& V) const;

    /* */
    bool normalize();
};
