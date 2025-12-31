


Vector3 Spring::force()
{
    return -1 * springCoefficient * (length * lengthInitial);
}
