import React from 'react';
import { Input } from '../Sakura';

export default {
  title: 'SAKURA/Input',
  component: Input 
};

const Template = (args) => <Input {...args} />

export const Default = Template.bind({});
Default.args = {
    label: 'nome',
    type: 'text',
    placeholder: 'Placeholder'
};
export const Password = Template.bind({});
Password.args = {
    label: 'password',
    type: 'password',
    placeholder: 'Password'
};
