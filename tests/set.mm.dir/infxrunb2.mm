include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cinf.mm"
include "cmnf.mm"
include "wceq.mm"
include "wa.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfral.mm"
include "simpl.mm"
include "wcel.mm"
include "mnfxr.mm"
include "a1i.mm"
include "wn.mm"
include "ssel2.mm"
include "nltmnf.mm"
include "syl.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "wi.mm"
include "ralimralim.mm"
include "adantl.mm"
include "infxr.mm"
include "ex.mm"
include "rexr.mm"
include "mnflt.mm"
include "eqbrtrd.mm"
include "adantll.mm"
include "wor.mm"
include "xrltso.mm"
include "xrinfmss.mm"
include "ad2antrr.mm"
include "infglb.mm"
include "mp2and.mm"
include "impbid.mm"

theorem infxrunb2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint A y
  disjoint A x
  disjoint x y
  disjoint A w
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  assert |- ( A C_ RR* -> ( A. x e. RR E. y e. A y < x <-> inf ( A , RR* , < ) = -oo ) )

  proof
    cA
    cxr
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    cA
    cxr
    clt
    cinf
    #
    cmnf
    wceq
    #
    @0
    @5
    @7
    @0
    @5
    wa
    #
    vx
    vy
    cA
    cmnf
    @0
    @5
    vx
    @0
    vx
    nfv
    @4
    vx
    cr
    nfra1
    nfan
    @0
    @5
    vy
    @0
    vy
    nfv
    @4
    vy
    vx
    cr
    vy
    cr
    nfcv
    @3
    vy
    cA
    nfre1
    nfral
    nfan
    @0
    @5
    simpl
    cmnf
    cxr
    wcel
    @8
    mnfxr
    a1i
    @0
    @2
    cmnf
    clt
    wbr
    wn
    #
    vx
    cA
    wral
    @5
    @0
    @9
    vx
    cA
    @0
    @2
    cA
    wcel
    wa
    @2
    cxr
    wcel
    #
    @9
    cA
    cxr
    @2
    ssel2
    @2
    nltmnf
    syl
    ralrimiva
    adantr
    @5
    cmnf
    @2
    clt
    wbr
    #
    @4
    wi
    vx
    cr
    wral
    @0
    @4
    @11
    vx
    cr
    ralimralim
    adantl
    infxr
    ex
    @0
    @7
    @5
    @0
    @7
    wa
    #
    @4
    vx
    cr
    @12
    @2
    cr
    wcel
    #
    wa
    #
    @10
    @6
    @2
    clt
    wbr
    #
    @4
    @13
    @10
    @12
    @2
    rexr
    adantl
    @7
    @13
    @15
    @0
    @7
    @13
    wa
    @6
    cmnf
    @2
    clt
    @7
    @13
    simpl
    @13
    @11
    @7
    @2
    mnflt
    adantl
    eqbrtrd
    adantll
    @14
    vz
    vw
    vy
    cxr
    cA
    @2
    clt
    cxr
    clt
    wor
    @14
    xrltso
    a1i
    @0
    vw
    cv
    #
    vz
    cv
    #
    clt
    wbr
    wn
    vw
    cA
    wral
    @17
    @16
    clt
    wbr
    @1
    @16
    clt
    wbr
    vy
    cA
    wrex
    wi
    vw
    cxr
    wral
    wa
    vz
    cxr
    wrex
    @7
    @13
    vz
    vw
    vy
    cA
    xrinfmss
    ad2antrr
    infglb
    mp2and
    ralrimiva
    ex
    impbid
end
