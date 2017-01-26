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
    ensures banner in availableBanners
    {
        availableBanners := adService.addBanner(banner, availableBanners);
    }
    
    method stopPublish (publisher: Publisher) //wrapper method for stopPublishAndFreeBanner (just to keep pointer for banner in the post-condition)
    modifies this
    requires adService != null
    requires publisher in ads && ads[publisher] != null
    {
      stopPublishAndFreeBanner(publisher, ads[publisher].banner);
    }
    
    method stopPublishAndFreeBanner (publisher: Publisher, banner : Banner) 
    modifies this
    requires adService != null    
    ensures publisher !in publishers
    ensures publisher !in ads
    ensures banner in availableBanners
    {
      publishers := adService.removePublisher(publisher, publishers);
      availableBanners := adService.addBanner(banner, availableBanners);
      ads := adService.removeAdOfPublisher(publisher, ads);      
    }
    
    method startPublish (publisher : Publisher, price : int) 
    modifies this
    requires adService != null  
    requires forall p :: p in publishers ==> p != null && p in ads && ads[p] != null && ads[p].banner != null
    requires forall banner :: banner in availableBanners ==> banner != null  
    {
      if (|availableBanners| > 0)
      {
        publishers := adService.addPublisher(publisher, publishers);
        if (availableBanners[0] != null) // need to be deleted but how to solve pre? 
        {
        ads := adService.addAd(publisher, price, availableBanners[0], ads);          
        }
        availableBanners := adService.popFirstBanner(availableBanners);               
      } 
      else
      {
        if (|publishers| > 0)
        {
          var minPublisher, minPrice := adService.findMinPublisher(publishers, ads);
          if (price > minPrice) 
          {
            ads := adService.addAd(publisher, price, ads[minPublisher].banner, ads); 
            ads := adService.removeAdOfPublisher(minPublisher, ads);   
            publishers := adService.removePublisher(minPublisher, publishers);   
            publishers := adService.addPublisher(publisher, publishers);            
          }
        }
      }
    }    
}



class AdvertisingService 
{

    constructor () 
    {
      
    }
    
    method addBanner(banner : Banner, banners : seq<Banner>) returns (retBanners : seq<Banner>)
    ensures banner in retBanners
    {
        return banners + [banner];
    }
    
    method removeAdOfPublisher(publisher : Publisher, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    ensures publisher !in retAds
    {
      return map p | p in ads && p != publisher :: ads[p];
    }
    
    method removePublisher(publisher : Publisher, publishers : seq<Publisher>) returns (retPublishers : seq<Publisher>)
    ensures publisher !in retPublishers
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

        return newPublishers;
    }
    
    method addPublisher (publisher : Publisher, publishers : seq<Publisher>) returns (retPublishers : seq<Publisher>)
    ensures publisher in retPublishers
    {
      return publishers + [publisher];     
    }
    
    method addAd (publisher : Publisher, price : int, banner : Banner, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    requires banner != null;
    ensures publisher in retAds && retAds[publisher] != null
    ensures retAds[publisher].price == price && retAds[publisher].banner == banner
    {
      var newAd : Ad := new Ad(banner, price);
      return ads[publisher := newAd]; 
    }
    
    method popFirstBanner(banners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires |banners| > 0;
    {
      return banners[1..];
    }
    
    method findMinPublisher(publishers : seq<Publisher>, ads : map <Publisher, Ad>) returns (retPublisher : Publisher, retPrice : int)
    requires |publishers| > 0
    requires forall p :: p in publishers ==> p != null && p in ads && ads[p] != null && ads[p].banner != null
    ensures retPublisher in ads
    ensures retPublisher != null && ads[retPublisher] != null && ads[retPublisher].banner != null
    {
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
      return minPublisher, minPrice;
    }

    
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



