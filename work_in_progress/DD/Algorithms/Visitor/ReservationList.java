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