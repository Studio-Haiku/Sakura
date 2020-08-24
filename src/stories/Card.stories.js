import React from 'react';

import { 
    Card,
    Row,
    Col
} from '../Sakura';

export default {
	title: 'SAKURA/Card',
	component: Card
};

const Template = (args) => (
    <Row>
        <Col size='3'/>
        <Col size='6'>
            <Card {...args}>
                <p>Test</p>
            </Card>
        </Col>
    </Row>
); 

export const Default = Template.bind({});
Default.args = {};
