import React from 'react';

import { Button } from '../Sakura';

export default {
  title: 'SAKURA/Button',
  component: Button
};

const Template = (args) => <Button {...args} />;

export const Primary = Template.bind({});
Primary.args = {
  color: 'primary',
  label: 'Button',
};

export const Secondary = Template.bind({});
Secondary.args = {
  color: 'secondary',
  label: 'Button',
};

export const Empty = Template.bind({});
Empty.args = {
  color: 'empty',
  label: 'Button',
};

export const Small = Template.bind({});
Small.args = {
  size: 'small',
  label: 'Small Button',
};

export const Default = Template.bind({});
Default.args = {
  size: 'default',
  label: 'Default Button',
};

export const Big = Template.bind({});
Big.args = {
  size: 'big',
  label: 'Big Button',
};


export const Block = Template.bind({});
Block.args = {
  size: 'block',
  label: 'Block Button',
};
