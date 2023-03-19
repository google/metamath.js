include "ct1.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "ctop.mm"
include "t1top.mm"
include "toptopon.mm"
include "sylib.mm"
include "ist1-2.mm"
include "syl.mm"
include "ibi.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem t1sep2
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume t1sep.1: |- X = U. J

  disjoint A o
  disjoint B o
  disjoint J o
  disjoint X o
  disjoint o x
  disjoint o y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  assert |- ( ( J e. Fre /\ A e. X /\ B e. X ) -> ( A. o e. J ( A e. o -> B e. o ) -> A = B ) )

  proof
    cJ
    ct1
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    vo
    cv
    #
    wcel
    #
    cB
    @3
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    cA
    cB
    wceq
    #
    wi
    #
    @0
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    @10
    @12
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @9
    @0
    @18
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @0
    @18
    wb
    @0
    cJ
    ctop
    wcel
    @19
    cJ
    t1top
    cJ
    cX
    t1sep.1
    toptopon
    sylib
    vx
    vy
    vo
    cJ
    cX
    ist1-2
    syl
    ibi
    @17
    @9
    @4
    @13
    wi
    #
    vo
    cJ
    wral
    #
    cA
    @12
    wceq
    #
    wi
    vx
    vy
    cA
    cB
    cX
    cX
    @10
    cA
    wceq
    #
    @15
    @21
    @16
    @22
    @23
    @14
    @20
    vo
    cJ
    @23
    @11
    @4
    @13
    @10
    cA
    @3
    eleq1
    imbi1d
    ralbidv
    @10
    cA
    @12
    eqeq1
    imbi12d
    @12
    cB
    wceq
    #
    @21
    @7
    @22
    @8
    @24
    @20
    @6
    vo
    cJ
    @24
    @13
    @5
    @4
    @12
    cB
    @3
    eleq1
    imbi2d
    ralbidv
    @12
    cB
    cA
    eqeq2
    imbi12d
    rspc2v
    mpan9
    3impb
end
