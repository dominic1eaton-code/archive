/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

struct LinearColor
{
    /* */
    float r,
          g,
          b,
          a;

    /* */
    inline LinearColor operator+(float scale) const;

    /* */
    inline LinearColor operator-(float scale) const;

    /* */
    inline LinearColor operator*(float scale) const;

    /* */
    inline LinearColor operator/(float scale) const;

    /* */
    inline LinearColor operator+(const LinearColor& C) const;

    /* */
    inline LinearColor operator-(const LinearColor& C) const;

    /* */
    inline LinearColor operator*(const LinearColor& C) const;

    /* */
    inline LinearColor operator/(const LinearColor& C) const;

    /* */
    inline LinearColor operator==(const LinearColor& C) const;

    /* */
    inline LinearColor operator!=(const LinearColor& C) const;

};
