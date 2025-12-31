/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */


namespace Mathlib
{
struct Qauternion
{
    /* */
    float x,
          y,
          z,
          w;

    /* */
    inline Qauternion operator+(float scale) const;

    /* */
    inline Qauternion operator-(float scale) const;

    /* */
    inline Qauternion operator*(float scale) const;

    /* */
    inline Qauternion operator/(float scale) const;

    /* */
    inline Qauternion operator+(const Qauternion& Q) const;

    /* */
    inline Qauternion operator-(const Qauternion& Q) const;

    /* */
    inline Qauternion operator*(const Qauternion& Q) const;

    /* */
    inline Qauternion operator/(const Qauternion& Q) const;

    /* */
    inline Qauternion operator==(const Qauternion& Q) const;

    /* */
    inline Qauternion operator!=(const Qauternion& Q) const;

    /* */
    bool normalize();

};
} // Mathlib