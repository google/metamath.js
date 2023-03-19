include "wcel.mm"
include "wa.mm"
include "caov.mm"
include "cop.mm"
include "cxp.mm"
include "opelxp.mm"
include "cdm.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wn.mm"
include "wceq.mm"
include "ndmaov.mm"
include "eleq1.mm"
include "biimpd.mm"
include "vprc.mm"
include "pm2.21i.mm"
include "syl6com.mm"
include "mpsyl.mm"
include "sylnbi.mm"
include "sylnbir.mm"
include "pm2.61i.mm"

theorem ndmaovcl
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume ndmaov.1: |- dom F = ( S X. S )
  assume ndmaovcl.2: |- ( ( A e. S /\ B e. S ) -> (( A F B )) e. S )
  assume ndmaovcl.3: |- (( A F B )) e. _V


  assert |- (( A F B )) e. S

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cA
    cB
    cF
    caov
    #
    cS
    wcel
    #
    ndmaovcl.2
    @0
    cA
    cB
    cop
    #
    cS
    cS
    cxp
    #
    wcel
    #
    @2
    cA
    cB
    cS
    cS
    opelxp
    @5
    @3
    cF
    cdm
    #
    wcel
    #
    @2
    @4
    @6
    @3
    @6
    @4
    ndmaov.1
    eqcomi
    eleq2i
    @1
    cvv
    wcel
    #
    @7
    wn
    @1
    cvv
    wceq
    #
    @2
    ndmaovcl.3
    cA
    cB
    cF
    ndmaov
    @9
    @8
    cvv
    cvv
    wcel
    #
    @2
    @9
    @8
    @10
    @1
    cvv
    cvv
    eleq1
    biimpd
    @10
    @2
    vprc
    pm2.21i
    syl6com
    mpsyl
    sylnbi
    sylnbir
    pm2.61i
end
