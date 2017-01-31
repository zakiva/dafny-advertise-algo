function isPublisherOut (publisher : Publisher, ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
{
	publisher !in publishers && publisher !in ads
}

function arePublishersInBothLists (ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
{
	(forall p :: p in publishers ==> p in ads) && (forall p :: p in ads ==> p in publishers)
}

function valuesOfAds (myAds : map<Publisher, Ad>) : set<Ad>
{
	set p: Publisher | p in myAds :: myAds[p]
}

function isNoNullPublishers (ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
requires arePublishersInBothLists(ads, publishers)
reads valuesOfAds(ads)
{
	forall p :: p in publishers ==> p != null && ads[p] != null && ads[p].banner != null
}

function isNoNullAds (ads: map <Publisher, Ad>) : bool
{
	forall p :: p in ads ==> ads[p] != null
}

function isNoNullAvailableBanners (availableBanners: seq<Banner>) : bool
{
	forall i :: 0 <= i < |availableBanners| ==> availableBanners[i] != null
}

function isUniqueAvailableBanners (availableBanners: seq<Banner>) : bool
{
	|availableBanners| > 0 ==> availableBanners[0] !in availableBanners[1..]
}

function isPublisherInMap (publisher : Publisher, retAds: map <Publisher, Ad>) : bool
{
	publisher in retAds && retAds[publisher] != null
}

function checkStartPublishRoomInAvailableBanners(publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
reads valuesOfAds(retAds)
{
	|availableBanners| > 0 ==> publisher in retPublishers && publisher in retAds && retAds[publisher] != null && retAds[publisher].price == price  && availableBanners[0] == retAds[publisher].banner && retBanners == availableBanners[1..] && availableBanners[0] !in retBanners
}

function checkStartPublishAllListsEmpty (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
{
	(|availableBanners| == 0 && |publishers| == 0) ==> publishers == retPublishers && ads == retAds && availableBanners == retBanners && publisher !in publishers && publisher !in ads
}

function checkStartPublishBidAccepted (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>, globalMinPublisher: Publisher) : bool
reads valuesOfAds(retAds)
reads valuesOfAds(ads)
requires forall p :: p in ads ==> ads[p] != null
{
	(|availableBanners| == 0 && |publishers| > 0 && !isPriceLessThanMinPrice(price, ads)) ==> (publisher in retPublishers && isPublisherInMap(publisher, retAds) && retAds[publisher].price == price && availableBanners == retBanners) && (globalMinPublisher !in retPublishers && globalMinPublisher !in retAds && globalMinPublisher in ads && retAds[publisher].banner == ads[globalMinPublisher].banner)
}

function isPriceLessThanMinPrice (price : int, ads: map <Publisher, Ad>) : bool
reads valuesOfAds(ads)
//requires forall p :: p in ads ==> ads[p] != null
{
	forall p :: p in ads && ads[p] != null ==> ads[p].price >= price
}

function checkStartPublishBidNotAccepted (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
reads valuesOfAds(ads)
{
	(|availableBanners| == 0 && |publishers| > 0 && isPriceLessThanMinPrice(price, ads)) ==> publishers == retPublishers && ads == retAds && availableBanners == retBanners && isPublisherOut(publisher, ads, publishers)
}

function isNoNull (availableBanners: seq<Banner>, publishers : seq<Publisher>, ads : map <Publisher, Ad>)  : bool
reads valuesOfAds(ads)
requires arePublishersInBothLists(ads, publishers)
{
	isNoNullPublishers(ads,publishers) && isNoNullAds(ads) && isNoNullAvailableBanners(availableBanners)
}

function adExists(adService : AdvertisingService, publisher: Publisher, ads: map <Publisher, Ad>, availableBanners: seq<Banner>) : bool
reads valuesOfAds(ads)
{
	adService != null  && isPublisherInMap(publisher, ads) && ads[publisher].banner !in availableBanners 
}

function startPublishCorrectChanges (publisher: Publisher, availableBanners: seq<Banner>, publishers : seq<Publisher>, ads : map <Publisher, Ad>)  : bool
reads valuesOfAds(ads)
{
	isPublisherOut(publisher, ads, publishers) && arePublishersInBothLists(ads, publishers) && isUniqueAvailableBanners(availableBanners) 
}

function findMinPublisherPreConditions(publishers : seq<Publisher>, ads : map <Publisher, Ad>) : bool 
reads valuesOfAds(ads)
{
	|publishers| > 0 && forall p :: p in publishers ==> p != null && p in ads && ads[p] != null && ads[p].banner != null && arePublishersInBothLists(ads, publishers) && isNoNullAds(ads)
}

function findMinPublisherPostConditions(retPrice : int, retPublisher : Publisher, publishers : seq<Publisher>, ads : map <Publisher, Ad>) : bool 
requires forall p :: p in ads ==> ads[p] != null
reads valuesOfAds(ads)
{
	retPublisher in ads && retPublisher in publishers && retPublisher != null && ads[retPublisher] != null && ads[retPublisher].banner != null && ads[retPublisher].price == retPrice && forall p :: p in ads ==> ads[p].price >= retPrice
}

function startPublishPostConditions(publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>, globalMinPublisher: Publisher) : bool
reads valuesOfAds(retAds)
reads valuesOfAds(ads)
requires forall p :: p in ads ==> ads[p] != null
{
	checkStartPublishRoomInAvailableBanners(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners)
	&& checkStartPublishBidNotAccepted(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners)
	&& checkStartPublishBidAccepted(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners, globalMinPublisher)
	&& checkStartPublishAllListsEmpty(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners)
}

function removePublisherInvPublisherOut(index: int, publishers: seq<Publisher>, newPublishers: seq<Publisher>, publisher: Publisher) : bool
{
	0 <= index <= |publishers| && publisher !in newPublishers
}

function removePublisherInvRestIn(index: int, publishers: seq<Publisher>, newPublishers: seq<Publisher>, publisher: Publisher) : bool
requires index <= |publishers|
{
	forall i :: 0 <= i < index && publishers[i] != publisher ==> publishers[i] in newPublishers
}


function findMinPublisherInvDataStructuresOk(minPrice: int, ads : map <Publisher, Ad>, index: int, publishers: seq<Publisher>, minPublisher: Publisher) : bool
reads valuesOfAds(ads)
{
	forall p :: p in publishers ==> p in ads && minPublisher in ads && ads[minPublisher] != null && ads[minPublisher].price == minPrice && minPublisher in publishers
}

function findMinPublisherInvMinPriceCorrect(minPrice: int, ads : map <Publisher, Ad>, index: int, publishers: seq<Publisher>, minPublisher: Publisher) : bool
requires isNoNullAds(ads)
requires arePublishersInBothLists(ads, publishers)
reads valuesOfAds(ads)
{
	0 <= index <= |publishers| && minPublisher in ads && forall i :: 0 <= i < index ==> minPrice <= ads[publishers[i]].price && isNoNullAds(ads)
}



class AdvertisingManager {

    var availableBanners: seq<Banner>;

    var publishers: seq<Publisher>;

    var ads: map <Publisher, Ad>;

    var adService : AdvertisingService;

    constructor()
    modifies this;
    {
        availableBanners := [];
        publishers := [];
        ads := map[];
        adService := new AdvertisingService ();
    }

    method addBanner(banner : Banner)
    modifies this
    requires adService != null
    requires banner !in availableBanners
    //ensures banner in availableBanners
    {
        availableBanners := adService.addBanner(banner, availableBanners);
    }
    
    /*    
    method stopPublish (publisher: Publisher) //wrapper method for stopPublishAndFreeBanner (just to keep pointer for banner in the post-condition)
    modifies this
    requires adService != null
    requires publisher in ads && ads[publisher] != null
    requires ads[publisher].banner !in availableBanners 
	ensures publisher !in publishers
    ensures publisher !in ads
    {
      stopPublish(publisher, ads[publisher].banner);
    }
    */
    
    method stopPublish (publisher: Publisher) 
    modifies this
	requires adExists(adService, publisher, ads, availableBanners)
    //requires banner !in availableBanners    
    //ensures publisher !in publishers
    //ensures publisher !in ads
    //ensures banner in availableBanners
    {
      publishers := adService.removePublisher(publisher, publishers);
      availableBanners := adService.addBanner(ads[publisher].banner, availableBanners);
      ads := adService.removeAdOfPublisher(publisher, ads);      
    }
    
    method startPublish (publisher : Publisher, price : int) 
    modifies this
    modifies adService
	requires arePublishersInBothLists(ads, publishers)
	requires isNoNull (availableBanners, publishers, ads) &&  adService != null
	requires startPublishCorrectChanges(publisher, availableBanners, publishers, ads)
    {
        publishers, ads, availableBanners := adService.startPublish(publisher, price, publishers, ads, availableBanners);
    }
	
	method isInPublishers(publisher : Publisher) returns (status : bool)
	ensures publisher in publishers ==> status == true
	ensures publisher !in publishers ==> status == false
	{
		return publisher in publishers;
	}        
}

class AdvertisingService 
{
    var globalMinPublisher: Publisher;

    constructor () 
    {  
    }

	//function isInside (b: Banner, s: seq<Banner>) : bool
    //{
      //b in s
    //}
    
    method addBanner(banner : Banner, banners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires banner !in banners
    ensures banner in retBanners
    {
        return banners + [banner];
    }
    
    method removeAdOfPublisher(publisher : Publisher, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    ensures publisher !in retAds
    ensures forall p :: p in ads && p != publisher ==> p in retAds && retAds[p] == ads[p]
    {
      return map p | p in ads && p != publisher :: ads[p];
    }
    
    method removePublisher(publisher : Publisher, publishers : seq<Publisher>) returns (retPublishers : seq<Publisher>)
    ensures publisher !in retPublishers
    ensures forall p :: p in publishers && p != publisher ==> p in retPublishers
    {
        var index := 0;
        var newPublishers : seq<Publisher> := [];
        while (index < |publishers|)
        decreases |publishers| - index // not needed - but it seems more complicated :)
        invariant removePublisherInvPublisherOut(index, publishers, newPublishers, publisher)
        invariant removePublisherInvRestIn(index, publishers, newPublishers, publisher)
        {
            if (publishers[index] != publisher)
            {
                newPublishers := newPublishers + [publishers[index]];
            }
            index := index + 1;
        }

        return newPublishers;
    }
    
    method addPublisher (publisher : Publisher, publishers : seq<Publisher>) returns (retPublishers : seq<Publisher>)
    ensures publisher in retPublishers
	ensures forall p :: p in publishers ==> p in retPublishers
    {
      return publishers + [publisher];     
    }
    
    method addAd (publisher : Publisher, price : int, banner : Banner, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    requires banner != null; 
    ensures isPublisherInMap(publisher, retAds)
    ensures retAds[publisher].price == price && retAds[publisher].banner == banner
    {
      var newAd : Ad := new Ad(banner, price);
      return ads[publisher := newAd]; 
    }
    
    method popFirstBanner(banners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires |banners| > 0
    requires banners[0] !in banners[1..] //- need to ensures it in a more general way ==> I THINK ITS OK NOW 
    ensures banners[0] !in retBanners    // - need to ensures it in a more general way ==> I THINK ITS OK NOW 
	ensures retBanners == banners[1..]
    {
      return banners[1..];
    }

	//function checkInvariantFindMinPublisher(index: int, publishers : seq<Publisher>, ads : map <Publisher, Ad>, minPublisher: Publisher, minPrice: int): bool
	//{
		//(forall p :: p in publishers ==> p in ads && minPublisher in ads && ads[minPublisher] != null && ads[minPublisher].price == minPrice && minPublisher in publishers) && (0 <= index <= |publishers| && minPublisher in ads && forall i :: 0 <= i < index ==> minPrice <= ads[publishers[i]].price && forall p :: p in ads ==> ads[p] != null)
	//}  
    
    // WE CAN NOW CHANGE THIS METHOD TO USE THE NEW FUNCTIONS - BUT IT MAY CHANGE THE CONDITIONS :( 
    method findMinPublisher(publishers : seq<Publisher>, ads : map <Publisher, Ad>) returns (retPublisher : Publisher, retPrice : int)
	requires findMinPublisherPreConditions(publishers, ads)
	requires forall p :: p in ads ==> ads[p] != null
	ensures findMinPublisherPostConditions(retPrice, retPublisher, publishers, ads)
    {
      var minPublisher := publishers[0];
      var minPrice := ads[minPublisher].price;

      var index := 1;
      while (index < |publishers|)
      decreases |publishers| - index
	  invariant findMinPublisherInvDataStructuresOk(minPrice, ads, index, publishers, minPublisher)
	  invariant findMinPublisherInvMinPriceCorrect(minPrice, ads, index, publishers, minPublisher)
	  // checkInvariantFindMinPublisher(index, publishers, ads,minPublisher, minPrice);
	  {
        var curPrice := ads[publishers[index]].price;
        if (curPrice < minPrice)
        {
          minPrice := curPrice;
          minPublisher := publishers[index];
        }
        index := index + 1;
      }
      return minPublisher, minPrice;
    }    
    

/*
    // need to add ensures...     
    function minPublisherFunc (publishers : seq<Publisher>, ads : map<Publisher, Ad>, tempMin : Publisher) : Publisher
    reads valuesOfAds(ads)
    requires forall p :: p in publishers ==> p in ads && ads[p] != null
    requires forall p :: p in ads ==> ads[p] != null
    requires tempMin in ads && ads[tempMin] != null
    ensures minPublisherFunc(publishers, ads, tempMin) in ads && ads[minPublisherFunc(publishers, ads, tempMin)] != null
    ensures forall p :: p in publishers ==> ads[p].price >= ads[minPublisherFunc(publishers, ads, tempMin)].price
    {
      if publishers == [] then tempMin else minPublisherFunc(publishers[1..], ads, minFunc(tempMin, publishers[0], ads))
    }
    
    function minFunc (p1 : Publisher, p2 : Publisher, ads : map<Publisher, Ad>) : Publisher
    reads valuesOfAds(ads)
    requires p1 in ads && p2 in ads && ads[p1] != null && ads[p2] != null
    {
      if ads[p1].price <= ads[p2].price then p1 else p2
    }
    */
    





    method startPublish(publisher : Publisher, price : int, publishers : seq<Publisher>, ads : map <Publisher, Ad>, availableBanners : seq<Banner>) returns (retPublishers : seq<Publisher>, retAds : map <Publisher, Ad>, retBanners : seq<Banner>)
    modifies this
	
	requires startPublishCorrectChanges(publisher, availableBanners, publishers, ads)
	requires isNoNull (availableBanners, publishers, ads) 
	ensures startPublishPostConditions(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners, globalMinPublisher);

	{
      var newPublishers : seq<Publisher> := publishers;
      var newAds : map <Publisher, Ad> := ads;
      var newBanners : seq<Banner> := availableBanners;
      
      if (|availableBanners| > 0)
      {
        newPublishers := addPublisher(publisher, newPublishers);
        newAds := addAd(publisher, price, newBanners[0], newAds);          
        newBanners := popFirstBanner(newBanners);               
      } 
      else
      {
        if (|newPublishers| > 0)
        {
          var minPublisher, minPrice := findMinPublisher(newPublishers, newAds);
          globalMinPublisher := minPublisher;
          if (price > minPrice) 
          {
            var banner := newAds[minPublisher].banner;
            newAds := addAd(publisher, price, banner, newAds);
            newAds := removeAdOfPublisher(minPublisher, newAds);   
            newPublishers := addPublisher(publisher, newPublishers); 
            newPublishers := removePublisher(minPublisher, newPublishers);   
          }
        }
      }  
      
     return newPublishers, newAds, newBanners; 
    }        
        
}

class Publisher
{
    constructor () 
    {
    }
}

class Banner
{
    constructor () 
    {
    }
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
    }
    
    /* THESE GETTERS ONLY CAUSE PROBLEMS 

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
    */
}



