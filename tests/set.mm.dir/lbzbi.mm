include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cz.mm"
include "nfv.mm"
include "nfre1.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "clt.mm"
include "btwnz.mm"
include "simpld.mm"
include "ssel2.mm"
include "w3a.mm"
include "zre.mm"
include "ltleletr.mm"
include "syl3an1.mm"
include "expd.mm"
include "3expia.mm"
include "syl5.mm"
include "expdimp.mm"
include "com23.mm"
include "imp.mm"
include "ralrimiv.mm"
include "ralim.mm"
include "syl.mm"
include "ex.mm"
include "anasss.mm"
include "expcom.mm"
include "imdistand.mm"
include "weq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6.mm"
include "ancomsd.mm"
include "rexlimdv.mm"
include "mpdi.mm"
include "rexlimd.mm"
include "zssre.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "impbid1.mm"

theorem lbzbi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- ( A C_ RR -> ( E. x e. RR A. y e. A x <_ y <-> E. x e. ZZ A. y e. A x <_ y ) )

  proof
    cA
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @4
    vx
    cz
    wrex
    #
    @0
    @4
    @6
    vx
    cr
    @0
    vx
    nfv
    @4
    vx
    cz
    nfre1
    @0
    @4
    @1
    cr
    wcel
    #
    @6
    @0
    @4
    @7
    @6
    wi
    @0
    @4
    wa
    #
    @7
    vz
    cv
    #
    @1
    clt
    wbr
    #
    vz
    cz
    wrex
    #
    @6
    @7
    @11
    @1
    @9
    clt
    wbr
    vz
    cz
    wrex
    vz
    vz
    @1
    btwnz
    simpld
    @7
    @8
    @11
    @6
    wi
    #
    @7
    @0
    @4
    @12
    @7
    @0
    wa
    #
    @4
    wa
    @10
    @6
    vz
    cz
    @13
    @4
    @9
    cz
    wcel
    #
    @10
    @6
    wi
    #
    @13
    @14
    @4
    @15
    @13
    @10
    @14
    @4
    wa
    #
    @6
    @13
    @10
    @16
    @6
    wi
    @13
    @10
    wa
    #
    @16
    @14
    @9
    @2
    cle
    wbr
    #
    vy
    cA
    wral
    #
    wa
    @6
    @17
    @14
    @4
    @19
    @13
    @10
    @14
    @4
    @19
    wi
    #
    wi
    @13
    @14
    @10
    @20
    @14
    @13
    @10
    @20
    wi
    #
    @14
    @7
    @0
    @21
    @14
    @7
    wa
    #
    @0
    wa
    #
    @10
    @20
    @23
    @10
    wa
    #
    @3
    @18
    wi
    #
    vy
    cA
    wral
    @20
    @24
    @25
    vy
    cA
    @23
    @10
    @2
    cA
    wcel
    #
    @25
    wi
    @23
    @26
    @10
    @25
    @22
    @0
    @26
    @10
    @25
    wi
    #
    @0
    @26
    wa
    @2
    cr
    wcel
    #
    @22
    @27
    cA
    cr
    @2
    ssel2
    @14
    @7
    @28
    @27
    @14
    @7
    @28
    w3a
    @10
    @3
    @18
    @14
    @9
    cr
    wcel
    @7
    @28
    @10
    @3
    wa
    @18
    wi
    @9
    zre
    @9
    @1
    @2
    ltleletr
    syl3an1
    expd
    3expia
    syl5
    expdimp
    com23
    imp
    ralrimiv
    @3
    @18
    vy
    cA
    ralim
    syl
    ex
    anasss
    expcom
    com23
    imp
    imdistand
    @4
    @19
    vx
    @9
    cz
    vx
    vz
    weq
    @3
    @18
    vy
    cA
    @1
    @9
    @2
    cle
    breq1
    ralbidv
    rspcev
    syl6
    ex
    com23
    ancomsd
    expdimp
    rexlimdv
    anasss
    expcom
    mpdi
    ex
    com23
    rexlimd
    cz
    cr
    wss
    @6
    @5
    wi
    zssre
    @4
    vx
    cz
    cr
    ssrexv
    ax-mp
    impbid1
end
