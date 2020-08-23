import React from 'react';
import PropTypes from 'prop-types';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';

import { library } from '@fortawesome/fontawesome-svg-core';
import { fas } from '@fortawesome/free-solid-svg-icons';

import './Button.styles.scss';

library.add(fas);

const Button = ({handler, label, icon, color='primary', size='default', ...props}) => (
	<button 
		onClick={handler}
		className={`btn btn-${color} btn-size-${size}`} 
		{...props} >
			{ icon && 
				<span>
					<FontAwesomeIcon icon={icon} size='lg'/>
				</span>
			}
		{label}
	</button>
);


Button.propTypes = {
	label: PropTypes.string,
	color: PropTypes.oneOf(['primary', 'secondary', 'empty']),
	size: PropTypes.oneOf(['small', 'default', 'big']),
	icon: PropTypes.string
};

Button.defaultProps = {
	label: 'Bottone',
	color: 'primary',
	size: 'default',
	icon: 'coffee'
};

export default Button;
