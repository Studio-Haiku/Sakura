import React from 'react';
import PropTypes from 'prop-types';
import './Input.styles.scss';

const Input = ({handler, label, ...props}) => { 
    return (
        <label>
            <input 
                onChange={handler} 
                className={`inpt inpt-border-default`} 
                {...props} required/>
            <span className='lbl'>{label}</span>
        </label>
    );
}

Input.propTypes = {
    label: PropTypes.string,
    placeholder: PropTypes.string
};

Input.defaultProps = {
    label: 'input',
    placeholder: 'Placeholder'
};


export default Input;
