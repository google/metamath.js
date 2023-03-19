include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "wne.mm"
include "cr.mm"
include "wi.mm"
include "zre.mm"
include "clt.mm"
include "wb.mm"
include "0re.mm"
include "ltnle.mm"
include "mpan2.mm"
include "adantr.mm"
include "anbi1d.mm"
include "ltletr.mm"
include "mp3an2.mm"
include "sylbird.mm"
include "ancoms.mm"
include "ancomsd.mm"
include "ltne.mm"
include "ex.mm"
include "adantl.mm"
include "syld.mm"
include "syl2an.mm"
include "impcom.mm"
include "znegcl.mm"
include "zneo.mm"
include "sylan2.mm"
include "wceq.mm"
include "cc.mm"
include "2cn.mm"
include "zcn.mm"
include "mulneg12.mm"
include "sylancr.mm"
include "oveq1d.mm"
include "neeqtrrd.mm"
include "2thd.mm"
include "necon4bid.mm"

theorem znnenlem
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( 0 <_ x /\ -. 0 <_ y ) /\ ( x e. ZZ /\ y e. ZZ ) ) -> ( x = y <-> ( 2 x. x ) = ( ( -u 2 x. y ) + 1 ) ) )

  proof
    cc0
    vx
    cv
    #
    cle
    wbr
    #
    cc0
    vy
    cv
    #
    cle
    wbr
    wn
    #
    wa
    #
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    wa
    #
    @0
    @2
    c2
    @0
    cmul
    co
    #
    c2
    cneg
    @2
    cmul
    co
    #
    c1
    caddc
    co
    #
    @8
    @0
    @2
    wne
    #
    @9
    @11
    wne
    #
    @7
    @4
    @12
    @5
    @0
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @4
    @12
    wi
    @6
    @0
    zre
    @2
    zre
    @14
    @15
    wa
    #
    @4
    @2
    @0
    clt
    wbr
    #
    @12
    @16
    @3
    @1
    @17
    @15
    @14
    @3
    @1
    wa
    #
    @17
    wi
    @15
    @14
    wa
    #
    @18
    @2
    cc0
    clt
    wbr
    #
    @1
    wa
    #
    @17
    @19
    @20
    @3
    @1
    @15
    @20
    @3
    wb
    #
    @14
    @15
    cc0
    cr
    wcel
    #
    @22
    0re
    @2
    cc0
    ltnle
    mpan2
    adantr
    anbi1d
    @15
    @23
    @14
    @21
    @17
    wi
    0re
    @2
    cc0
    @0
    ltletr
    mp3an2
    sylbird
    ancoms
    ancomsd
    @15
    @17
    @12
    wi
    @14
    @15
    @17
    @12
    @2
    @0
    ltne
    ex
    adantl
    syld
    syl2an
    impcom
    @7
    @13
    @4
    @7
    @9
    c2
    @2
    cneg
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @11
    @6
    @5
    @24
    cz
    wcel
    @9
    @26
    wne
    @2
    znegcl
    @0
    @24
    zneo
    sylan2
    @7
    @10
    @25
    c1
    caddc
    @6
    @10
    @25
    wceq
    #
    @5
    @6
    c2
    cc
    wcel
    @2
    cc
    wcel
    @27
    2cn
    @2
    zcn
    c2
    @2
    mulneg12
    sylancr
    adantl
    oveq1d
    neeqtrrd
    adantl
    2thd
    necon4bid
end
