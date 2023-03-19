include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "clt.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wn.mm"
include "csup.mm"
include "wceq.mm"
include "wb.mm"
include "ssel2.mm"
include "xrlenlt.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "anbi1d.mm"
include "biimpa.mm"
include "supxr.mm"
include "syldan.mm"

theorem supxr2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  assert |- ( ( ( A C_ RR* /\ B e. RR* ) /\ ( A. x e. A x <_ B /\ A. x e. RR ( x < B -> E. y e. A x < y ) ) ) -> sup ( A , RR* , < ) = B )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wcel
    #
    wa
    #
    vx
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @3
    cB
    clt
    wbr
    @3
    vy
    cv
    clt
    wbr
    vy
    cA
    wrex
    wi
    vx
    cr
    wral
    #
    wa
    #
    cB
    @3
    clt
    wbr
    wn
    #
    vx
    cA
    wral
    #
    @6
    wa
    #
    cA
    cxr
    clt
    csup
    cB
    wceq
    @2
    @7
    @10
    @2
    @5
    @9
    @6
    @2
    @4
    @8
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    @1
    @4
    @8
    wb
    #
    @0
    @11
    wa
    @3
    cxr
    wcel
    @1
    @12
    cA
    cxr
    @3
    ssel2
    @3
    cB
    xrlenlt
    sylan
    an32s
    ralbidva
    anbi1d
    biimpa
    vx
    vy
    cA
    cB
    supxr
    syldan
end
