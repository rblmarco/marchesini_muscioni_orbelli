public Interface ListCreator{
	
	public void accept(ListCreatorVisitor visitor);
	public void composeList();
}