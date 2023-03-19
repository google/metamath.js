include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cgcd.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cdvds.mm"
include "wa.mm"
include "1z.mm"
include "gcddvds.mm"
include "mpan2.mm"
include "simprd.mm"
include "cn.mm"
include "wi.mm"
include "cc0.mm"
include "wn.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "simpr.mm"
include "necon3ai.mm"
include "ax-mp.mm"
include "gcdn0cl.mm"
include "nnzd.mm"
include "1nn.mm"
include "dvdsle.mm"
include "sylancl.mm"
include "mpd.mm"
include "wb.mm"
include "nnle1eq1.mm"
include "syl.mm"
include "mpbid.mm"

theorem gcd1
  let cM: class M


  assert |- ( M e. ZZ -> ( M gcd 1 ) = 1 )

  proof
    cM
    cz
    wcel
    #
    cM
    c1
    cgcd
    co
    #
    c1
    cle
    wbr
    #
    @1
    c1
    wceq
    #
    @0
    @1
    c1
    cdvds
    wbr
    #
    @2
    @0
    @1
    cM
    cdvds
    wbr
    #
    @4
    @0
    c1
    cz
    wcel
    #
    @5
    @4
    wa
    1z
    cM
    c1
    gcddvds
    mpan2
    simprd
    @0
    @1
    cz
    wcel
    c1
    cn
    wcel
    @4
    @2
    wi
    @0
    @1
    @0
    @6
    @1
    cn
    wcel
    #
    1z
    @0
    @6
    wa
    cM
    cc0
    wceq
    #
    c1
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @7
    c1
    cc0
    wne
    @11
    ax-1ne0
    @10
    c1
    cc0
    @8
    @9
    simpr
    necon3ai
    ax-mp
    cM
    c1
    gcdn0cl
    mpan2
    mpan2
    #
    nnzd
    1nn
    @1
    c1
    dvdsle
    sylancl
    mpd
    @0
    @7
    @2
    @3
    wb
    @12
    @1
    nnle1eq1
    syl
    mpbid
end
