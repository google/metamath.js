include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cun.mm"
include "cpr.mm"
include "c2.mm"
include "wcel.mm"
include "wceq.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "3nn0.mm"
include "1le3.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "fzsplit.mm"
include "ax-mp.mm"
include "1e0p1.mm"
include "oveq2i.mm"
include "cz.mm"
include "0z.mm"
include "fzpr.mm"
include "0p1e1.mm"
include "preq2i.mm"
include "3eqtri.mm"
include "1p1e2.mm"
include "df-3.mm"
include "oveq12i.mm"
include "2z.mm"
include "2p1e3.mm"
include "uneq12i.mm"
include "eqtri.mm"

theorem fz0to3un2pr



  assert |- ( 0 ... 3 ) = ( { 0 , 1 } u. { 2 , 3 } )

  proof
    cc0
    c3
    cfz
    co
    #
    cc0
    c1
    cfz
    co
    #
    c1
    c1
    caddc
    co
    #
    c3
    cfz
    co
    #
    cun
    #
    cc0
    c1
    cpr
    #
    c2
    c3
    cpr
    #
    cun
    c1
    @0
    wcel
    #
    @0
    @4
    wceq
    @7
    c1
    cn0
    wcel
    c3
    cn0
    wcel
    c1
    c3
    cle
    wbr
    1nn0
    3nn0
    1le3
    c1
    c3
    elfz2nn0
    mpbir3an
    c1
    cc0
    c3
    fzsplit
    ax-mp
    @1
    @5
    @3
    @6
    @1
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    cc0
    @8
    cpr
    #
    @5
    c1
    @8
    cc0
    cfz
    1e0p1
    oveq2i
    cc0
    cz
    wcel
    @9
    @10
    wceq
    0z
    cc0
    fzpr
    ax-mp
    @8
    c1
    cc0
    0p1e1
    preq2i
    3eqtri
    @3
    c2
    c2
    c1
    caddc
    co
    #
    cfz
    co
    #
    c2
    @11
    cpr
    #
    @6
    @2
    c2
    c3
    @11
    cfz
    1p1e2
    df-3
    oveq12i
    c2
    cz
    wcel
    @12
    @13
    wceq
    2z
    c2
    fzpr
    ax-mp
    @11
    c3
    c2
    2p1e3
    preq2i
    3eqtri
    uneq12i
    eqtri
end
