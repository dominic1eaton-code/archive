/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

#include "Qauternion.h"
#include "Vector.h"

struct Rotation
{
    /* */
    float yaw,
          pitch,
          roll;

    /* */
    inline Rotation operator+(float scale) const;

    /* */
    inline Rotation operator-(float scale) const;

    /* */
    inline Rotation operator*(float scale) const;

    /* */
    inline Rotation operator/(float scale) const;

    /* */
    inline Rotation operator+(const Rotation& R) const;

    /* */
    inline Rotation operator-(const Rotation& R) const;

    /* */
    inline Rotation operator*(const Rotation& R) const;

    /* */
    inline Rotation operator/(const Rotation& R) const;

    /* */
    inline Rotation operator==(const Rotation& R) const;

    /* */
    inline Rotation operator!=(const Rotation& R) const;

    /* */
    Qauternion quaternion() const;

    /* */
    Vector euler() const;
};
