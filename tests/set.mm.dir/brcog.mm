include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "ccom.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "bi2anan9.mm"
include "exbidv.mm"
include "df-co.mm"
include "brabga.mm"

theorem brcog
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  assert |- ( ( A e. V /\ B e. W ) -> ( A ( C o. D ) B <-> E. x ( A D x /\ x C B ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cD
    wbr
    #
    @1
    vz
    cv
    #
    cC
    wbr
    #
    wa
    #
    vx
    wex
    cA
    @1
    cD
    wbr
    #
    @1
    cB
    cC
    wbr
    #
    wa
    #
    vx
    wex
    vy
    vz
    cA
    cB
    cC
    cD
    ccom
    cV
    cW
    @0
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    @5
    @8
    vx
    @9
    @2
    @6
    @10
    @4
    @7
    @0
    cA
    @1
    cD
    breq1
    @3
    cB
    @1
    cC
    breq2
    bi2anan9
    exbidv
    vy
    vz
    vx
    cC
    cD
    df-co
    brabga
end
