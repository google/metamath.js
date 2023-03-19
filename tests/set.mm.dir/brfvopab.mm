include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "wa.mm"
include "copab.mm"
include "breqd.mm"
include "brabv.mm"
include "syl6bi.mm"
include "imdistani.mm"
include "3anass.mm"
include "sylibr.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "fvprc.mm"
include "breq.mm"
include "br0.mm"
include "pm2.21i.mm"
include "syl.mm"
include "pm2.61i.mm"

theorem brfvopab
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume brfvopab.1: |- ( X e. _V -> ( F ` X ) = { <. y , z >. | ph } )


  assert |- ( A ( F ` X ) B -> ( X e. _V /\ A e. _V /\ B e. _V ) )

  proof
    cX
    cvv
    wcel
    #
    cA
    cB
    cX
    cF
    cfv
    #
    wbr
    #
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    w3a
    #
    wi
    #
    @0
    @2
    @5
    @0
    @2
    wa
    @0
    @3
    @4
    wa
    #
    wa
    @5
    @0
    @2
    @7
    @0
    @2
    cA
    cB
    wph
    vy
    vz
    copab
    #
    wbr
    @7
    @0
    @1
    @8
    cA
    cB
    brfvopab.1
    breqd
    wph
    vy
    vz
    cA
    cB
    brabv
    syl6bi
    imdistani
    @0
    @3
    @4
    3anass
    sylibr
    ex
    @0
    wn
    @1
    c0
    wceq
    #
    @6
    cX
    cF
    fvprc
    @9
    @2
    cA
    cB
    c0
    wbr
    #
    @5
    cA
    cB
    @1
    c0
    breq
    @10
    @5
    cA
    cB
    br0
    pm2.21i
    syl6bi
    syl
    pm2.61i
end
