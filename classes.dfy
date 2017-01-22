class Publisher {
  constructor(){
    boardPublishedIn := null;
  }
  var boardPublishedIn: Board;
  
  method sendProposal(s: Server)
  {
    assert boardPublishedIn == null;
	var isSucceed := s.getProposal(this);
  }
  
  method cancelPublish()
  {
    assert boardPublishedIn != null;
	this.boardPublishedIn.currentPublisher := null;
	this.boardPublishedIn := null;
  }
}

class Board {
  constructor(){
    currentPublisher := null;
  }
  var currentPublisher: Publisher;
  
  method initBoard(s: Server)
  {
    s.allBoards := s.allBoards[s.counter := this];
	s.counter := s.counter + 1;
  }
}

class Server {
  constructor(){
    counter := 0;
  }
  var counter : int;
  var allBoards: map<int,Board>;
  
  method getProposal(publisher: Publisher) returns (success: bool)
  {
	var a := 0;
	while (a < counter){
	  if (allBoards[a].currentPublisher == null){
	    allBoards[a].currentPublisher := publisher;
		publisher.boardPublishedIn := allBoards[a];
		return true;
	  }
	}
	return false;
  }
}