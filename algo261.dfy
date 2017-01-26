class AdvertisingManager {

    var availableBanners: seq<Banner>;
    
    var availableBannersSize: int;

    var publishers: seq<Publisher>;
    
    var globalMinPublisher: Publisher;

    var ads: map <Publisher, Ad>;

    constructor()
    modifies this;
    {
        availableBanners := [];
        publishers := [];
        ads := map[];
        globalMinPublisher := null;
    }
    
   

    method startPublish(publisher: Publisher, price: int)
    modifies this;
    requires publisher != null;
    requires publisher !in publishers;
    requires publisher !in ads;
    requires forall banner :: banner in availableBanners  ==> banner != null
	requires |availableBanners| > 0
	requires availableBanners[0] != null

	ensures availableBannersSize > 0 ==> publisher in publishers && publisher in ads
  
  ensures availableBannersSize == 0 && !isPriceLessThanMinPrice(price, ads)  ==> publisher in publishers && publisher in ads && globalMinPublisher !in ads
  
  ensures availableBannersSize == 0 && isPriceLessThanMinPrice(price, ads) ==> publisher !in publishers && publisher !in ads 
  //needs to ensures no changes in last one 
  
    {
      
      availableBannersSize := |availableBanners|;
      
      
        if (|availableBanners| > 0) {
        var newAd : Ad := new Ad(availableBanners[0], price); // create a new ad
        ads := ads[publisher := newAd]; // add the new ad
        publishers := publishers + [publisher]; //add the publisher
        availableBanners := availableBanners[1..]; // make the publisher's banner unavailable
        // note: if not "atomic" need to do it more safely
    }
    else {
      
      if (	|publishers| > 0) {
	    var minPublisher := publishers[0];
        var minPrice := ads[minPublisher].price;

        var index := 1;
        while (index < |publishers|)
        decreases |publishers| - index
        invariant   minPublisher in publishers && 0 <= index <= |publishers| && minPublisher in ads && forall i :: 0 <= i < index ==> minPrice <= ads[publishers[i]].price //&& forall i :: 0 <= i < index ==> ads[minPublisher].price <= ads[publishers[i]].price
        {
            var curPrice := ads[publishers[index]].price;
            if (curPrice < minPrice)
            {
                minPrice := curPrice;
                minPublisher := publishers[index];
            }
            index := index + 1;
        }
        
        globalMinPublisher := minPublisher; 

        if (price > minPrice)
        {
			     replaceMin(minPublisher, publisher, price);
        }
        
    }
    }

    }
    
    
    function isPriceLessThanMinPrice (price : int, ads: map <Publisher, Ad>) : bool
    reads valuesOfAds(ads)
    //requires forall p :: p in ads ==> ads[p] != null
    {
      forall p :: p in ads && ads[p] != null ==> ads[p].price >= price
    }
    
    function valuesOfAds (myAds : map<Publisher, Ad>) : set<Ad>
    {
      set p: Publisher | p in myAds :: myAds[p]
    }
    
    method replaceMin (minPublisher: Publisher, publisher : Publisher, price : int)
    modifies this
    requires publisher != null
    requires publisher !in publishers
    requires publisher !in ads
	requires minPublisher != null
	requires minPublisher in publishers
  	requires minPublisher in ads
    requires forall p :: p in publishers ==> p != null
    requires forall p :: p in publishers ==> p in ads
    requires forall p :: p in ads ==> ads[p] != null
    requires forall p :: p in ads ==> ads[p].banner != null
    requires |publishers| > 0
    requires globalMinPublisher == minPublisher
        ensures globalMinPublisher == minPublisher
	ensures minPublisher !in publishers
	ensures minPublisher !in ads
	 ensures publisher in publishers
	 ensures publisher in ads


    // need to fix the errors here: ensures !isPriceLessThanMinPrice(price, ads) ==> publisher in publishers
    //VERY BAD : //ensures forall p :: !(p in ads && ads[p] != null && ads[p].price >= price && p == publisher) ==> p !in publishers && p !in ads // && .... 
    {

                  
            var newAd : Ad := new Ad(ads[minPublisher].banner, price); // create a new ad 
            
                              ads:= map p | p in ads && p != minPublisher :: ads[p]; // remove the ad
                              
                              
            ads := ads[publisher := newAd]; // add the new ad
            publishers := publishers + [publisher]; //add the publisher

            removePublisherFromPublishers(minPublisher, publisher);
	}




 

    method stopPublish(publisher: Publisher)
    modifies this;
    requires publisher != null;
    requires publisher in ads;
    requires publisher in publishers;
    requires ads[publisher] != null
    requires forall p :: p in publishers ==> ads[publisher].banner != null && ads[publisher].banner !in availableBanners
    requires forall p :: p in ads ==> ads[p] != null
    ensures publisher !in ads;
    ensures publisher !in publishers;
    {
        var banner := ads[publisher].getBanner();
        //assert banner !in availableBanners;
        //freeBanner(banner); its the same as addBanner 
        addBanner(banner, publisher);
        ads:= map p | p in ads && p != publisher :: ads[p]; // remove the ad
        // note: if not "atomic" need to do it more safely


        removePublisherFromPublishersForStop(publisher);

    } 
    

    method removePublisherFromPublishers (publisher: Publisher, newPublisher : Publisher)
    modifies this;
    requires publisher != null;
    requires newPublisher in ads
        requires newPublisher in publishers
    requires publisher in publishers;
    requires publisher !in ads;
    requires forall p :: p in ads ==> ads[p] != null
        requires globalMinPublisher == publisher
        ensures globalMinPublisher == publisher
    ensures publisher !in publishers;
    ensures newPublisher in publishers;
    ensures newPublisher in ads;
    ensures publisher !in ads;
    ensures forall p :: p in ads ==> ads[p] != null

    {
        var index := 0;
        var newPublishers : seq<Publisher> := [];
        while (index < |publishers|)
        decreases |publishers| - index // not needed - but it seems more complicated :) 
        invariant 0 <= index <= |publishers| && publisher !in newPublishers && forall i :: 0 <= i < index ==> publishers[i] in newPublishers || publishers[i] == publisher // index bounds not needed - but it seems more complicated :) 
        {
            if (publishers[index] != publisher)
            {
                newPublishers := newPublishers + [publishers[index]];
            }
            index := index + 1;
        }

        publishers := newPublishers;
    }
    
    
    method removePublisherFromPublishersForStop (publisher: Publisher)
    modifies this;
    requires publisher != null;

    requires publisher in publishers;
    requires publisher !in ads;
    requires forall p :: p in ads ==> ads[p] != null
    ensures publisher !in publishers;

    ensures publisher !in ads;
    ensures forall p :: p in ads ==> ads[p] != null

    {
        var index := 0;
        var newPublishers : seq<Publisher> := [];
        while (index < |publishers|)
        decreases |publishers| - index // not needed - but it seems more complicated :) 
        invariant 0 <= index <= |publishers| && publisher !in newPublishers // index bounds not needed - but it seems more complicated :) 
        {
            if (publishers[index] != publisher)
            {
                newPublishers := newPublishers + [publishers[index]];
            }
            index := index + 1;
        }

        publishers := newPublishers;
    }
    
    

/*
    method freeBanner(banner : Banner) // this method has to be "private" so a banner can't call it and remove itself
    //this is actually does the same as addBanner
    // I added this only because I had a problem inside stopPublish
    modifies this;
    requires banner != null;
    requires banner !in availableBanners; //why it fails?
    ensures banner in availableBanners;
    {
      if (banner != null) 
      {
        availableBanners := availableBanners + [banner]; // make the publisher's banner available        
      }
    }
    
*/    

    method addBanner (banner : Banner, publisher : Publisher)
    modifies this;
    requires banner != null
    requires banner !in availableBanners;
    requires forall p :: p in ads ==> ads[p] != null
    requires publisher in publishers;
    ensures banner in availableBanners;
    ensures publisher in publishers;
    ensures forall p :: p in ads ==> ads[p] != null
    {
        availableBanners := availableBanners + [banner];
    }
    
    /*

    method removeBanner(banner: Banner)
    modifies this;
    {
        //this may be a little more complicated
    }
    */
}

class Publisher
{
    constructor () {}
}

class Banner
{
    constructor () {}
}

class Ad
{
    var banner : Banner;
    var price : int;

    constructor(bannerArg : Banner, priceArg : int)
    modifies this;
    requires bannerArg != null;
    ensures banner == bannerArg;
    ensures price == priceArg;
    {
        banner := bannerArg;
        price := priceArg;
        // this is very bad thing to do: 
       // if (banner == null)
        //{
       //   banner := new Banner();
       // }
    }

    method getBanner() returns (b: Banner)
    ensures b == banner;
    {
        return banner;
    }

    method getPrice() returns (p: int)
    ensures p == price;
    {
        return price;
    }
}


//try nat instead of int 
//getters problem - maybe we can just drop them and access directly
