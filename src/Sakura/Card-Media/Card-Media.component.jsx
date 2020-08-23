import React from 'react';
import './Card-Media.styles.scss';
import PropTypes from 'prop-types';

const CardMedia = ({image, round, ...props}) => (
    <div 
        className='sakura__card--media' 
        {...props}>
        <img 
            style={{borderRadius: round ? '0 0 0 0' : '10px 10px 0 0'}} 
            className='sakura__card--img'
            alt=""
            src={image}/>
    </div>
);

CardMedia.propTypes = {
    image: PropTypes.string 
};

CardMedia.defaultProps = {
    image: "https://via.placeholder.com/512"
}

export default CardMedia;
