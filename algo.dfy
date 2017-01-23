method Main() {
  print("start\n");
  
  var p : Publisher := new Publisher(100);
  
  var a : Advertise := new Advertise();
  
  print(p);
  print("\n");
  print(a.ads);
  print("\n");
  print(p.payment);
  print("\n");
  print(p !in a.ads);
  print("\n");
  
  
//  assert p !in a.ads; //why this considered as an assertion violation?  
//  a.startPublish(p);
  
  
  print("end\n");
}


class Advertise {
  
  var availableWebsites: seq<Website>;
   
  var ads: map <Publisher, Website>; 
  
  constructor()
  modifies this;
  {
    availableWebsites := [];
    ads := map[];
  }
  
  method startPublish(publisher: Publisher) 
  modifies this; 
  requires publisher !in ads; 
  {
    if (availableWebsites != []) {
      ads := ads[publisher := availableWebsites[0]]; // add the ad
      availableWebsites := availableWebsites[1..]; // make the publisher's website unavailable
      // note: if not "atomic" need to do it more safely 
    }
    else {
      // TODO: search for the min and replace it if worth it 
    }
    
  }
  
  method stopPublish(publisher: Publisher)
  modifies this;
  requires publisher in ads; 
  {
    availableWebsites := availableWebsites + [ads[publisher]]; // make the publisher's website available
    ads:= map p | p in ads && p != publisher :: ads[p]; // remove the ad
    // note: if not "atomic" need to do it more safely 
  }
   
  method addWebsite (website: Website)
  modifies this;
  {
    availableWebsites := availableWebsites + [website];
  }
  
  method removeWebsite(website: Website)
  modifies this;
  {
    //this may be a little more complicated 
  }
}

class Publisher 
{  
  var payment : int;
  
  constructor(p : int)
  modifies this;
  {
    payment := p;
  }
}

class Website 
{
}

