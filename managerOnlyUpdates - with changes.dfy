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
    requires adService != null && banner !in availableBanners
    {
        availableBanners := adService.addBanner(banner, availableBanners);
    }

    method removeBanner(banner : Banner)
    modifies this
    requires adService != null && banner in availableBanners
    {
        availableBanners := adService.removeBanner(banner, availableBanners);
    }

    method stopPublish (publisher: Publisher)
    modifies this
    requires adExists(adService, publisher, ads, availableBanners) && adService != null
    {
        publishers := adService.removePublisher(publisher, publishers);
        availableBanners := adService.addBanner(ads[publisher].banner, availableBanners);
        ads := adService.removeAdOfPublisher(publisher, ads);
    }

    method startPublish (publisher : Publisher, price : int)
    modifies this
    modifies adService
    requires startPublishRequirements(publisher, availableBanners, publishers, ads)
    requires isNoNull (availableBanners, publishers, ads) &&  adService != null
    {
        publishers, ads, availableBanners := adService.startPublish(publisher, price, publishers, ads, availableBanners);
    }

    method isPublishing(publisher : Publisher) returns (status : bool)
    requires adsKeysEqualsPublishers (ads, publishers)
    ensures publisher in publishers <==> status == true
    {
        return publisher in publishers;
    }

    method isBannerAvailable(banner : Banner) returns (status : bool)
    ensures banner in availableBanners <==> status == true
    {
        return banner in availableBanners;
    }
}

class AdvertisingService
{
    var globalMinPublisher: Publisher;

    constructor ()
    {
    }

    method addBanner(banner : Banner, banners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires banner !in banners
    ensures banner in retBanners
    {
        return banners + [banner];
    }

    method removeBanner(banner : Banner, availableBanners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires banner in availableBanners
    ensures bannerRemovedInvariant (banner, retBanners, availableBanners)
    {
        var index := 0;
        var newBanners : seq<Banner> := [];
        while (index < |availableBanners|)
        decreases |availableBanners| - index
        invariant removeBannerLoopInvariant(index, availableBanners, newBanners, banner)
        {
            if (availableBanners[index] != banner)
            {
                newBanners := newBanners + [availableBanners[index]];
            }
            index := index + 1;
        }
        return newBanners;
    }

    method removeAdOfPublisher(publisher : Publisher, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    ensures adRemovedInvariant(publisher, retAds, ads)
    {
        return map p | p in ads && p != publisher :: ads[p];
    }

    method removePublisher(publisher : Publisher, publishers : seq<Publisher>) returns (retPublishers : seq<Publisher>)
    ensures removePublisherInvariant(publisher, publishers, retPublishers)
    {
        var index := 0;
        var newPublishers : seq<Publisher> := [];
        while (index < |publishers|)
        decreases |publishers| - index
        invariant removePublisherLoopInvariant(index, publishers, newPublishers, publisher)
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
    ensures addPublisherInvariant(publisher, publishers, retPublishers)	
    {
        return publishers + [publisher];
    }

    method addAd (publisher : Publisher, price : int, banner : Banner, ads : map <Publisher, Ad>) returns (retAds : map <Publisher, Ad>)
    requires banner != null;
    ensures addAdInvariant(publisher, price, banner, retAds)
    {
        var newAd : Ad := new Ad(banner, price);
        return ads[publisher := newAd];
    }

    method popFirstBanner(banners : seq<Banner>) returns (retBanners : seq<Banner>)
    requires |banners| > 0 && banners[0] !in banners[1..]
    // requires banners[0] !in banners[1..]
    ensures banners[0] !in retBanners && retBanners == banners[1..]
    // ensures retBanners == banners[1..]
    {
        return banners[1..];
    }

    method findMinPublisher(publishers : seq<Publisher>, ads : map <Publisher, Ad>) returns (retPublisher : Publisher, retPrice : int)
    requires findMinPublisherRequirements(publishers, ads)
    ensures minPublisherFound(retPrice, retPublisher, publishers, ads)
    {
        var minPublisher := publishers[0];
        var minPrice := ads[minPublisher].price;

        var index := 1;
        while (index < |publishers|)
        decreases |publishers| - index
        invariant findMinPublisherLoopInvariant(minPrice, ads, index, publishers, minPublisher)
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

    method startPublish(publisher : Publisher, price : int, publishers : seq<Publisher>, ads : map <Publisher, Ad>, availableBanners : seq<Banner>) returns (retPublishers : seq<Publisher>, retAds : map <Publisher, Ad>, retBanners : seq<Banner>)
    modifies this
    requires startPublishRequirements(publisher, availableBanners, publishers, ads)
    requires isNoNull (availableBanners, publishers, ads)
    ensures startPublishInvariant(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners, globalMinPublisher);
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
    ensures banner == bannerArg && price == priceArg;
    {
        banner := bannerArg;
        price := priceArg;
    }
}

function isPublishing (publisher : Publisher, ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
		{
        publisher !in publishers &&
        publisher !in ads
        }

        function adsKeysEqualsPublishers (ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
        {
        (forall p :: p in publishers ==> p in ads) &&
        (forall p :: p in ads ==> p in publishers)
        }

        function valuesOfAds (myAds : map<Publisher, Ad>) : set<Ad>
        {
        set p: Publisher | p in myAds :: myAds[p]
        }

        function isNoNullPublishers (ads: map <Publisher, Ad>, publishers : seq<Publisher>) : bool
        requires adsKeysEqualsPublishers(ads, publishers)
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

        function isPublisherInAds (publisher : Publisher, retAds: map <Publisher, Ad>) : bool
		{
        publisher in retAds &&
        retAds[publisher] != null
        }

        function startPublishWithAvailableBanner(publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
		reads valuesOfAds(retAds)
        {
        |availableBanners| > 0 ==> publisher in retPublishers && 
		publisher in retAds && 
		retAds[publisher] != null && 
		retAds[publisher].price == price  && 
		availableBanners[0] == retAds[publisher].banner && 
		retBanners == availableBanners[1..] && 
		availableBanners[0] !in retBanners
        }

        function startPublishEmptyList (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
		{
        (|availableBanners| == 0 && 
		|publishers| == 0) ==> publishers == retPublishers && 
		ads == retAds && 
		availableBanners == retBanners && 
		publisher !in publishers && 
		publisher !in ads
        }

        function publishingStarted (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>, globalMinPublisher: Publisher) : bool
		reads valuesOfAds(retAds)
        reads valuesOfAds(ads)
        requires forall p :: p in ads ==> ads[p] != null
        {
        (|availableBanners| == 0 && 
		|publishers| > 0 && 
		!isPriceLessThanMinPrice(price, ads)) ==> (publisher in retPublishers && 
		isPublisherInAds(publisher, retAds) && 
		retAds[publisher].price == price && 
		availableBanners == retBanners) && 
		(globalMinPublisher !in retPublishers && 
		globalMinPublisher !in retAds && 
		globalMinPublisher in ads && 
		retAds[publisher].banner == ads[globalMinPublisher].banner)
        }

        function isPriceLessThanMinPrice (price : int, ads: map <Publisher, Ad>) : bool
        reads valuesOfAds(ads)
        {
        forall p :: p in ads && 
		ads[p] != null ==> ads[p].price >= price
        }

        function publishingNotStarted (publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>) : bool
		reads valuesOfAds(ads)
        {
        (|availableBanners| == 0 && 
		|publishers| > 0 && 
		isPriceLessThanMinPrice(price, ads)) ==> publishers == retPublishers && 
		ads == retAds && availableBanners == retBanners && 
		isPublishing(publisher, ads, publishers)
        }

        function isNoNull (availableBanners: seq<Banner>, publishers : seq<Publisher>, ads : map <Publisher, Ad>)  : bool
        reads valuesOfAds(ads)
        requires adsKeysEqualsPublishers(ads, publishers)
        {
        isNoNullPublishers(ads,publishers) && 
		isNoNullAds(ads) && 
		isNoNullAvailableBanners(availableBanners)
        }

        function adExists(adService : AdvertisingService, publisher: Publisher, ads: map <Publisher, Ad>, availableBanners: seq<Banner>) : bool
        reads valuesOfAds(ads)
        {
        isPublisherInAds(publisher, ads) && 
		ads[publisher].banner !in availableBanners
        }

        function startPublishRequirements (publisher: Publisher, availableBanners: seq<Banner>, publishers : seq<Publisher>, ads : map <Publisher, Ad>)  : bool
        reads valuesOfAds(ads)
        {
        isPublishing(publisher, ads, publishers) && 
		adsKeysEqualsPublishers(ads, publishers) && 
		isUniqueAvailableBanners(availableBanners) && 
		adsKeysEqualsPublishers(ads, publishers)
        }

        function findMinPublisherRequirements(publishers : seq<Publisher>, ads : map <Publisher, Ad>) : bool
		reads valuesOfAds(ads)
        {
        |publishers| > 0 && 
		forall p :: p in publishers ==> p != null && 
		p in ads && ads[p] != null && 
		ads[p].banner != null && 
		adsKeysEqualsPublishers(ads, publishers) && 
		isNoNullAds(ads) &&
		(forall p :: p in ads ==> ads[p] != null)
        }

        function minPublisherFound(retPrice : int, retPublisher : Publisher, publishers : seq<Publisher>, ads : map <Publisher, Ad>) : bool
		requires findMinPublisherRequirements(publishers, ads)
        reads valuesOfAds(ads)
        {
        retPublisher in ads && 
		retPublisher in publishers && 
		retPublisher != null && 
		ads[retPublisher] != null && 
		ads[retPublisher].banner != null && 
		ads[retPublisher].price == retPrice && 
		forall p :: p in ads ==> ads[p].price >= retPrice
        }

        function startPublishInvariant(publisher : Publisher, price : int, publishers : seq<Publisher>, retPublishers: seq<Publisher>, ads : map <Publisher, Ad>, retAds: map <Publisher, Ad>, availableBanners : seq<Banner>, retBanners: seq<Banner>, globalMinPublisher: Publisher) : bool
        reads valuesOfAds(retAds)
        reads valuesOfAds(ads)
        requires forall p :: p in ads ==> ads[p] != null
        {
        startPublishWithAvailableBanner(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners) && 
		publishingNotStarted(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners) && 
		publishingStarted(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners, globalMinPublisher) && 
		startPublishEmptyList(publisher, price, publishers, retPublishers, ads, retAds, availableBanners, retBanners)
        }

		function removePublisherLoopInvariant(index: int, publishers: seq<Publisher>, newPublishers: seq<Publisher>, publisher: Publisher) : bool
		{
        0 <= index <= |publishers| && 
		publisher !in newPublishers && 
		forall i :: 0 <= i < index && 
		publishers[i] != publisher ==> publishers[i] in newPublishers
        }


		function findMinPublisherLoopInvariant(minPrice: int, ads : map <Publisher, Ad>, index: int, publishers: seq<Publisher>, minPublisher: Publisher) : bool
        requires isNoNullAds(ads)
        requires adsKeysEqualsPublishers(ads, publishers)
        reads valuesOfAds(ads)
        {
        forall p :: p in publishers ==> p in ads && 
		minPublisher in ads && 
		ads[minPublisher] != null && 
		ads[minPublisher].price == minPrice && 
		minPublisher in publishers && 
		0 <= index <= |publishers| && 
		minPublisher in ads && 
		forall i :: 0 <= i < index ==> minPrice <= ads[publishers[i]].price && 
		isNoNullAds(ads)
        }

        function bannerRemovedInvariant(banner : Banner, retBanners : seq<Banner>, availableBanners : seq<Banner>) : bool
        {
        banner !in retBanners &&
        forall b :: b in availableBanners && b != banner ==> b in retBanners
        }

        function adRemovedInvariant(publisher : Publisher, retAds : map <Publisher, Ad>, ads : map <Publisher, Ad>) : bool
        {
        publisher !in retAds &&
        forall p :: p in ads && p != publisher ==> p in retAds && retAds[p] == ads[p]
        }

		function removePublisherInvariant(publisher : Publisher, publishers : seq<Publisher>, retPublishers : seq<Publisher>) : bool
		{
		publisher !in retPublishers && 
		forall p :: p in publishers && 
		p != publisher ==> p in retPublishers
		}

		function addPublisherInvariant(publisher : Publisher, publishers : seq<Publisher>, retPublishers : seq<Publisher>) : bool
		{
		publisher in retPublishers && 
		forall p :: p in publishers ==> p in retPublishers
		}

		function addAdInvariant(publisher : Publisher, price : int, banner : Banner, retAds : map <Publisher, Ad>) : bool
		reads valuesOfAds(retAds)
		{
		isPublisherInAds(publisher, retAds) && 
		retAds[publisher].price == price && 
		retAds[publisher].banner == banner
		}

		function removeBannerLoopInvariant(index: int, availableBanners: seq<Banner>, newBanners: seq<Banner>, banner: Banner) : bool
		{
		0 <= index <= |availableBanners| && banner !in newBanners && forall i :: 0 <= i < index && availableBanners[i] != banner ==> availableBanners[i] in newBanners
		}




