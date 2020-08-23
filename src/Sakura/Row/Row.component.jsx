import React from 'react';
import './Row.styles.scss';

const Row = ({children, ...props}) => (
	<div className='sakura__row' {...props}>
		{children}
	</div>
);

export default Row;