include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wn.mm"
include "wceq.mm"
include "ralnex.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ssel2.mm"
include "rexr.mm"
include "xrlenlt.mm"
include "con2bid.mm"
include "syl2an.mm"
include "an32s.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6rbb.mm"
include "ralbidva.mm"
include "syl5bbr.mm"
include "supxrunb2.mm"
include "supxrcl.mm"
include "nltpnft.mm"
include "syl.mm"
include "3bitrd.mm"
include "con4bid.mm"

theorem supxrbnd2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( A C_ RR* -> ( E. x e. RR A. y e. A y <_ x <-> sup ( A , RR* , < ) < +oo ) )

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
    cA
    cxr
    clt
    csup
    #
    cpnf
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
    cpnf
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
    @2
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
    @1
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
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    @19
    @15
    cA
    cxr
    @1
    ssel2
    @2
    rexr
    @20
    @21
    wa
    @3
    @9
    @1
    @2
    xrlenlt
    con2bid
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
    supxrunb2
    @0
    @6
    cxr
    wcel
    @12
    @13
    wb
    cA
    supxrcl
    @6
    nltpnft
    syl
    3bitrd
    con4bid
end
