include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmnf.mm"
include "clt.mm"
include "cinf.mm"
include "wn.mm"
include "wceq.mm"
include "ralnex.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ssel2.mm"
include "rexr.mm"
include "simpl.mm"
include "simpr.mm"
include "xrltnled.mm"
include "syl2an.mm"
include "an32s.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6rbb.mm"
include "ralbidva.mm"
include "syl5bbr.mm"
include "infxrunb2.mm"
include "infxrcl.mm"
include "ngtmnft.mm"
include "syl.mm"
include "3bitrd.mm"
include "con4bid.mm"

theorem infxrbnd2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A C_ RR* -> ( E. x e. RR A. y e. A x <_ y <-> -oo < inf ( A , RR* , < ) ) )

  proof
    cA
    cxr
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
    cmnf
    cA
    cxr
    clt
    cinf
    #
    clt
    wbr
    #
    @0
    @5
    wn
    #
    @2
    @1
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
    @6
    cmnf
    wceq
    #
    @7
    wn
    #
    @8
    @4
    wn
    #
    vx
    cr
    wral
    @0
    @11
    @4
    vx
    cr
    ralnex
    @0
    @14
    @10
    vx
    cr
    @0
    @1
    cr
    wcel
    #
    wa
    #
    @10
    @3
    wn
    #
    vy
    cA
    wrex
    @14
    @16
    @9
    @17
    vy
    cA
    @0
    @2
    cA
    wcel
    #
    @15
    @9
    @17
    wb
    #
    @0
    @18
    wa
    @2
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @19
    @15
    cA
    cxr
    @2
    ssel2
    @1
    rexr
    @20
    @21
    wa
    @2
    @1
    @20
    @21
    simpl
    @20
    @21
    simpr
    xrltnled
    syl2an
    an32s
    rexbidva
    @3
    vy
    cA
    rexnal
    syl6rbb
    ralbidva
    syl5bbr
    vx
    vy
    cA
    infxrunb2
    @0
    @6
    cxr
    wcel
    @12
    @13
    wb
    cA
    infxrcl
    @6
    ngtmnft
    syl
    3bitrd
    con4bid
end
