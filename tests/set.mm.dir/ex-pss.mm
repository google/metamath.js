include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "c3.mm"
include "ctp.mm"
include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "ex-ss.mm"
include "wcel.mm"
include "wn.mm"
include "3ex.mm"
include "tpid3.mm"
include "1re.mm"
include "1lt3.mm"
include "gtneii.mm"
include "2re.mm"
include "2lt3.mm"
include "nelpri.mm"
include "nelne1.mm"
include "mp2an.mm"
include "necomi.mm"
include "df-pss.mm"
include "mpbir2an.mm"

theorem ex-pss



  assert |- { 1 , 2 } C. { 1 , 2 , 3 }

  proof
    c1
    c2
    cpr
    #
    c1
    c2
    c3
    ctp
    #
    wpss
    @0
    @1
    wss
    @0
    @1
    wne
    ex-ss
    @1
    @0
    c3
    @1
    wcel
    c3
    @0
    wcel
    wn
    @1
    @0
    wne
    c1
    c2
    c3
    3ex
    tpid3
    c3
    c1
    c2
    c1
    c3
    1re
    1lt3
    gtneii
    c2
    c3
    2re
    2lt3
    gtneii
    nelpri
    c3
    @1
    @0
    nelne1
    mp2an
    necomi
    @0
    @1
    df-pss
    mpbir2an
end
