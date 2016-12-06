public class ListController extends ListCreatorVisitor{
	
	public void createList(ListCreator list){
		list.accept(this);
	}
}