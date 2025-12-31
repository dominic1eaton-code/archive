

Engine::Engine()
{

}

template<typename T>
void init(T modes)
{
    for (auto mode : modes)
    {
        modes[U] = new U();
    }


}


void cycle()
{
    m_strokes[StrokeType::INTAKE].execute();
    
    m_strokes[StrokeType::COMPRESSION].execute();

    m_strokes[StrokeType::POWER].execute();

    m_strokes[StrokeType::EXHAUST].execute();

}


