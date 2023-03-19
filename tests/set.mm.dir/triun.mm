include "wtr.mm"
include "wral.mm"
include "cv.mm"
include "ciun.mm"
include "wss.mm"
include "wcel.mm"
include "wrex.mm"
include "eliun.mm"
include "wa.mm"
include "r19.29.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfss.mm"
include "trss.mm"
include "imp.mm"
include "ssiun2.mm"
include "sstr2.mm"
include "syl2imc.mm"
include "rexlimi.mm"
include "syl.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "dftr3.mm"
include "sylibr.mm"

theorem triun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A Tr B -> Tr U_ x e. A B )

  proof
    cB
    wtr
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    vx
    cA
    cB
    ciun
    #
    wss
    #
    vy
    @3
    wral
    @3
    wtr
    @1
    @4
    vy
    @3
    @2
    @3
    wcel
    @1
    @2
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    vx
    @2
    cA
    cB
    eliun
    @1
    @6
    wa
    @0
    @5
    wa
    #
    vx
    cA
    wrex
    @4
    @0
    @5
    vx
    cA
    r19.29
    @7
    @4
    vx
    cA
    vx
    @2
    @3
    vx
    @2
    nfcv
    vx
    cA
    cB
    nfiu1
    nfss
    @7
    @2
    cB
    wss
    #
    vx
    cv
    cA
    wcel
    cB
    @3
    wss
    @4
    @0
    @5
    @8
    cB
    @2
    trss
    imp
    vx
    cA
    cB
    ssiun2
    @2
    cB
    @3
    sstr2
    syl2imc
    rexlimi
    syl
    sylan2b
    ralrimiva
    vy
    @3
    dftr3
    sylibr
end
