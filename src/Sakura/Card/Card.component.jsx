import React from 'react';

import Loader from  '../Loader';
import CardHeader from '../Card-Header';
import CardMedia from '../Card-Media';
import CardBody from '../Card-Body';
import PropTypes from 'prop-types';

import './Card.styles.scss';

const Card = ({loaderImg, loading, header, media, footer, children,...props}) => (
    <div className="haiku__card--container" {...props}>
        <div className="haiku__card">
            { loading && <Loader src={loaderImg}/>}
            { header && <CardHeader/> }
            { media && <CardMedia round={header}/> }
            { children && <CardBody>{children}</CardBody> }
        </div>
    </div>
);

Card.propTypes = {
    loaderImg: PropTypes.string,
    loading: PropTypes.bool,
    header: PropTypes.bool,
    media: PropTypes.bool,
};

Card.defaultProps = {
    loaderImg: 'logo_mini.svg',
    loading: true,
    header: false,
    media: false,
};

export default Card;
