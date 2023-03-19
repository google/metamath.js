include "cc.mm"
include "wss.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wb.mm"
include "cncfrss.mm"
include "adantl.mm"
include "simpl.mm"
include "elcncf2.mm"
include "syl2anc.mm"
include "cncfi.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "biantrud.mm"
include "bitr4d.mm"

theorem cncffvrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( C C_ CC /\ F e. ( A -cn-> B ) ) -> ( F e. ( A -cn-> C ) <-> F : A --> C ) )

  proof
    cC
    cc
    wss
    #
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    wa
    #
    cF
    cA
    cC
    ccncf
    co
    wcel
    #
    cA
    cC
    cF
    wf
    #
    vw
    cv
    #
    vx
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    @5
    cF
    cfv
    @6
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    #
    clt
    wbr
    wi
    vw
    cA
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    wa
    #
    @4
    @2
    cA
    cc
    wss
    #
    @0
    @3
    @10
    wb
    @1
    @11
    @0
    cA
    cB
    cF
    cncfrss
    adantl
    @0
    @1
    simpl
    vx
    vy
    vz
    vw
    cA
    cC
    cF
    elcncf2
    syl2anc
    @2
    @9
    @4
    @1
    @9
    @0
    @1
    @8
    vx
    vy
    cA
    crp
    @1
    @6
    cA
    wcel
    @7
    crp
    wcel
    @8
    vz
    vw
    cA
    cB
    @6
    @7
    cF
    cncfi
    3expb
    ralrimivva
    adantl
    biantrud
    bitr4d
end
