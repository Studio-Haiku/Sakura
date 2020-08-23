import React from 'react';
import './Col.styles.scss';

const Col = ({children, force, style, size = 12, ...props}) => (
    <div 
        className={  force ? '': 'sakura__col'}
        style={{gridColumn: `span ${size}`, ...style}}
        {...props} >
            {children}
    </div>
);
export default Col;
