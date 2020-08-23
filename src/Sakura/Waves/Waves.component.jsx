import React from 'react';
import Wave from 'react-wavify';

import './Waves.styles.scss';

const Waves = ({color = '#000000', height = 20, amplitude = 20, speed = 0.30, points = 3, ...props}) => (
    <div className="sakura__wave">
        <Wave fill={color} paused={false} options={{
            height,
            amplitude,
            speed,
            points 
        }} />
    </div>
);



export default Waves;
