include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cho.mm"
include "cfv.mm"
include "wceq.mm"
include "hmopadj.mm"
include "wa.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wral.mm"
include "dmadjop.mm"
include "adantr.mm"
include "adj1.mm"
include "3expb.mm"
include "adantlr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "elhmop.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem hmopadj2
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. dom adjh -> ( T e. HrmOp <-> ( adjh ` T ) = T ) )

  proof
    cT
    cado
    cdm
    wcel
    #
    cT
    cho
    wcel
    #
    cT
    cado
    cfv
    #
    cT
    wceq
    #
    cT
    hmopadj
    @0
    @3
    @1
    @0
    @3
    wa
    #
    chil
    chil
    cT
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    #
    @6
    cT
    cfv
    #
    @7
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @1
    @0
    @5
    @3
    cT
    dmadjop
    adantr
    @4
    @11
    vx
    vy
    chil
    chil
    @4
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    wa
    @8
    @6
    @2
    cfv
    #
    @7
    csp
    co
    #
    @10
    @0
    @14
    @8
    @16
    wceq
    #
    @3
    @0
    @12
    @13
    @17
    @6
    @7
    cT
    adj1
    3expb
    adantlr
    @3
    @16
    @10
    wceq
    @0
    @14
    @3
    @15
    @9
    @7
    csp
    @6
    @2
    cT
    fveq1
    oveq1d
    ad2antlr
    eqtrd
    ralrimivva
    vx
    vy
    cT
    elhmop
    sylanbrc
    ex
    impbid2
end
