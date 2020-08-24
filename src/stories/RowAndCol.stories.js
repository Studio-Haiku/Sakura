import React from 'react';

import {
	Row,
	Col
} from '../Sakura';

export default {
	title: 'SAKURA/Rows And Cols',
	component: Row
};

const Template = (args) => (
	<>
	<Row>
		<Col size='1' style={{backgroundColor: 'red'}}>
			<p>Col</p>
		</Col>
		<Col size='2' style={{backgroundColor: 'red'}}>
			<p>Col</p>
		</Col>
		<Col size='3' style={{backgroundColor: 'red'}}>
			<p>Col</p>
		</Col>
		<Col size='6' style={{backgroundColor: 'red'}}>
			<p>Col</p>
		</Col>
		<Col size='12' style={{backgroundColor: 'blue'}}>
			<p>Col</p>
		</Col>
	</Row>
	</>
);

export const Default = Template.bind({});
Default.args = {};