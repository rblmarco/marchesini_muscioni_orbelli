public abstract Class ListCreatorVisitor{
	
	public void visitListCreator();
}

public Interface ListCreator{
	
	public void accept(ListCreatorVisitor visitor);
	public void composeList();
}

public class ListController extends ListCreatorVisitor{
	
	public void createList(ListCreator list){
		list.accept(this);
	}
}

public class ReservationList implements ListCreator{
	
	@Override
	public void accept(ListCreatorVisitor visitor){
		
		visitor.visitListCreator(this);
	}
	
	@Override
	public void composeList(){
		
		//code that compose the list in the correct way
	}
}
