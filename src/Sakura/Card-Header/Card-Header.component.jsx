import React from 'react';

import Row from '../Row';
import Col from '../Col';

import PropTypes from 'prop-types';

import './Card-Header.styles.scss';

const CardHeader = ({title, subtitle, avatar, menu}) => (
    <div className="sakura__card--header">
        <Row>
            <Col size='3' force>
                <img className='sakura__card--avatar' alt="" src={avatar}/>
            </Col>
            <Col size='6' force className='test'>
                <p className='sakura__card--title'>{title}</p>
                <span className='sakura__card--subtitle'>{subtitle}</span>
            </Col>
            <Col size='3' force>
                { /* Spazio per menù */ }
            </Col>
        </Row>
    </div>
);

CardHeader.propTypes = {
    title: PropTypes.string,
    subtitle: PropTypes.string,
    avatar: PropTypes.string
};

CardHeader.defaultProps = {
    title: 'Titolo',
    subtitle: 'Sottotitolo',
    avatar: 'https://via.placeholder.com/60'
};

export default CardHeader;
