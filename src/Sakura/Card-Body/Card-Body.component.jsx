import React from 'react';

import PropTypes from 'prop-types';

import './Card-Body.styles.scss';

const CardBody = ({children, ...props}) => (
    <div className='sakura__card--body'>
        {children}
    </div>
);

CardBody.propTypes = {
    titolo: PropTypes.string,
};

CardBody.defaultProps = {
    titolo: 'Titolo di prova',
};

export default CardBody;
