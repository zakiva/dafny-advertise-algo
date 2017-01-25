//method Main() {
  /*
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
*/

class AdvertisingManager {

    var availableBanners: seq<Banner>;

    var publishers: seq<Publisher>;

    var ads: map <Publisher, Ad>;

    constructor()
    modifies this;
    {
        availableBanners := [];
        publishers := [];
        ads := map[];
    }

    method startPublish(publisher: Publisher, price: int)
    modifies this;
    requires publisher != null;
    requires publisher !in publishers;
    requires publisher !in ads;
    requires forall banner :: banner in availableBanners  ==> banner != null
    //ensuers ???
    {
        if (|availableBanners| > 0) {
        var newAd : Ad := new Ad(availableBanners[0], price); // create a new ad
        ads := ads[publisher := newAd]; // add the new ad
        publishers := publishers + [publisher]; //add the publisher
        availableBanners := availableBanners[1..]; // make the publisher's banner unavailable
        // note: if not "atomic" need to do it more safely
    }
    else {
        replaceMin(publisher, price);

        // TODO: make it smarter:  forall x :: x in a ==> 4 > x check min before!!
    }

    }

    method replaceMin (publisher : Publisher, price : int)
    requires publisher != null
    requires forall publisher :: publisher in publishers ==> publisher in ads
    requires forall ad :: ad in ads ==> ad != null
    requires |publishers| > 0
    //ensures???
    {
        var minPublisher := publishers[0];
        var minPrice := ads[minPublisher].price;

        var index := 1;
        while (index < |publishers|)
        //invariant 0 <= index < |publishers|
        {
            var curPrice := ads[publishers[index]].price;
            if (curPrice < minPrice)
            {
                minPrice := curPrice;
                minPublisher := publishers[index];
            }
            index := index + 1;
        }

        if (price > minPrice)
        {
            //add new ad with new publisher new price and same banner

            // CODE DUPLICATE
            var newAd : Ad := new Ad(ads[minPublisher].banner, price); // create a new ad
            ads := ads[publisher := newAd]; // add the new ad
            publishers := publishers + [publisher]; //add the publisher
            // CODE DUPLICATE



            //remove minPublisher from publishers

            removePublisherFromPublishers(minPublisher);

            //remove ad of minPubliushers from ads

            ads:= map p | p in ads && p != minPublisher :: ads[p]; // remove the ad

        }

    }






    method stopPublish(publisher: Publisher)
    modifies this;
    requires publisher != null;
    requires publisher in ads;
    requires publisher in publishers;
    requires ads[publisher] != null
    ensures publisher !in ads;
    ensures publisher !in publishers;
    {
        var banner := ads[publisher].getBanner();
        //assert banner !in availableBanners;
        freeBanner(banner);
        ads:= map p | p in ads && p != publisher :: ads[p]; // remove the ad
        // note: if not "atomic" need to do it more safely


        removePublisherFromPublishers(publisher);

    }

    method removePublisherFromPublishers (publisher: Publisher)
    modifies this;
    requires publisher != null;
    requires publisher in publishers;
    ensures publisher !in publishers;
    {
        var index := 0;
        var newPublishers : seq<Publisher> := [];
        while (index < |publishers|)
        {
            if (publishers[index] != publisher)
            {
                newPublishers := newPublishers + [publishers[index]];
            }
            index := index + 1;
        }

        publishers := newPublishers;
    }


    method freeBanner(banner : Banner) // this method has to be "private" so a banner can't call it and remove itself
    //this is actually does the same as addBanner
    // I added this only because I had a problem inside stopPublish
    modifies this;
    //requires banner != null;
    //requires banner !in availableBanners; //why it fails?
   // ensures banner in availableBanners;
    {
      if (banner != null) 
      {
        availableBanners := availableBanners + [banner]; // make the publisher's banner available        
      }
    }

    method addBanner (banner: Banner)
    modifies this;
    requires banner != null
    requires banner !in availableBanners;
    ensures banner in availableBanners;
    {
        availableBanners := availableBanners + [banner];
    }

    method removeBanner(banner: Banner)
    modifies this;
    {
        //this may be a little more complicated
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

//getters problem - maybe we can just drop them and access directly
