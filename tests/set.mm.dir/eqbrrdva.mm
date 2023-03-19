include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "ssbrd.mm"
include "brxp.mm"
include "syl6ib.mm"
include "wb.mm"
include "3expib.mm"
include "pm5.21ndd.mm"
include "eqbrrdv.mm"

theorem eqbrrdva
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqbrrdva.1: |- ( ph -> A C_ ( C X. D ) )
  assume eqbrrdva.2: |- ( ph -> B C_ ( C X. D ) )
  assume eqbrrdva.3: |- ( ( ph /\ x e. C /\ y e. D ) -> ( x A y <-> x B y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A = B )

  proof
    wph
    vx
    vy
    cA
    cB
    wph
    cA
    cvv
    cvv
    cxp
    #
    wss
    cA
    wrel
    wph
    cA
    cC
    cD
    cxp
    #
    @0
    eqbrrdva.1
    cC
    cD
    xpss
    #
    syl6ss
    cA
    df-rel
    sylibr
    wph
    cB
    @0
    wss
    cB
    wrel
    wph
    cB
    @1
    @0
    eqbrrdva.2
    @2
    syl6ss
    cB
    df-rel
    sylibr
    wph
    vx
    cv
    #
    cC
    wcel
    #
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    @3
    @5
    cA
    wbr
    #
    @3
    @5
    cB
    wbr
    #
    wph
    @8
    @3
    @5
    @1
    wbr
    #
    @7
    wph
    cA
    @1
    @3
    @5
    eqbrrdva.1
    ssbrd
    @3
    @5
    cC
    cD
    brxp
    #
    syl6ib
    wph
    @9
    @10
    @7
    wph
    cB
    @1
    @3
    @5
    eqbrrdva.2
    ssbrd
    @11
    syl6ib
    wph
    @4
    @6
    @8
    @9
    wb
    eqbrrdva.3
    3expib
    pm5.21ndd
    eqbrrdv
end
