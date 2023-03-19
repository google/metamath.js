include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cvbr.mm"
include "iman.mm"
include "anass.mm"
include "dfpss2.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "xchbinx.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6bbr.mm"

theorem cvbr2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A <oH B <-> ( A C. B /\ A. x e. CH ( ( A C. x /\ x C_ B ) -> x = B ) ) ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    cA
    cB
    ccv
    wbr
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    wpss
    #
    @1
    cB
    wpss
    #
    wa
    #
    vx
    cch
    wrex
    wn
    #
    wa
    @0
    @2
    @1
    cB
    wss
    #
    wa
    #
    @1
    cB
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    wa
    vx
    cA
    cB
    cvbr
    @10
    @5
    @0
    @10
    @4
    wn
    #
    vx
    cch
    wral
    @5
    @9
    @11
    vx
    cch
    @9
    @7
    @8
    wn
    #
    wa
    #
    @4
    @7
    @8
    iman
    @13
    @2
    @6
    @12
    wa
    #
    wa
    @4
    @2
    @6
    @12
    anass
    @3
    @14
    @2
    @1
    cB
    dfpss2
    anbi2i
    bitr4i
    xchbinx
    ralbii
    @4
    vx
    cch
    ralnex
    bitri
    anbi2i
    syl6bbr
end
