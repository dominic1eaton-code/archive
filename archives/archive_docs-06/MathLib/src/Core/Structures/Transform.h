/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

#include "Vector.h"
#include "Rotation.h"

struct Transform
{
    /* */
    Rotation rotation;

    /* */
    Vector translation;

    /* */
    Vector scale;

    /* */
    inline Transform operator==(const Transform& V) const;

    /* */
    inline Transform operator!=(const Transform& V) const;

};
