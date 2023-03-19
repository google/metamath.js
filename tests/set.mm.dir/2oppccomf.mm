include "ccomf.mm"
include "cfv.mm"
include "coppc.mm"
include "wceq.mm"
include "wtru.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "chom.mm"
include "wral.mm"
include "cbs.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "oppcbas.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "oppcco.mm"
include "eqtr2d.mm"
include "ralrimivw.mm"
include "ralrimivvva.mm"
include "eqidd.mm"
include "2oppcbas.mm"
include "a1i.mm"
include "chomf.mm"
include "2oppchomf.mm"
include "comfeq.mm"
include "mpbird.mm"
include "trud.mm"

theorem 2oppccomf
  let cC: class C
  let cO: class O
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppcbas.1: |- O = ( oppCat ` C )


  assert |- ( comf ` C ) = ( comf ` ( oppCat ` O ) )

  proof
    cC
    ccomf
    cfv
    cO
    coppc
    cfv
    #
    ccomf
    cfv
    wceq
    #
    wtru
    @1
    vg
    cv
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    @2
    @3
    @6
    @7
    @0
    cco
    cfv
    #
    co
    co
    #
    wceq
    #
    vg
    @5
    @7
    cC
    chom
    cfv
    #
    co
    #
    wral
    #
    vf
    @4
    @5
    @13
    co
    #
    wral
    #
    vz
    cC
    cbs
    cfv
    #
    wral
    vy
    @18
    wral
    vx
    @18
    wral
    wtru
    @17
    vx
    vy
    vz
    @18
    @18
    @18
    wtru
    @4
    @18
    wcel
    #
    @5
    @18
    wcel
    #
    @7
    @18
    wcel
    #
    w3a
    wa
    #
    @15
    vf
    @16
    @22
    @12
    vg
    @14
    @22
    @11
    @3
    @2
    @7
    @5
    cop
    @4
    cO
    cco
    cfv
    #
    co
    co
    @9
    @22
    @18
    cO
    @23
    @3
    @2
    @0
    @4
    @5
    @7
    @18
    cC
    cO
    oppcbas.1
    @18
    eqid
    #
    oppcbas
    @23
    eqid
    @0
    eqid
    wtru
    @19
    @20
    @21
    simpr1
    #
    wtru
    @19
    @20
    @21
    simpr2
    #
    wtru
    @19
    @20
    @21
    simpr3
    #
    oppcco
    @22
    @18
    cC
    @8
    @2
    @3
    cO
    @7
    @5
    @4
    @24
    @8
    eqid
    #
    oppcbas.1
    @27
    @26
    @25
    oppcco
    eqtr2d
    ralrimivw
    ralrimivw
    ralrimivvva
    wtru
    vx
    vy
    vz
    @18
    cC
    @0
    @10
    @8
    vf
    vg
    @13
    @28
    @10
    eqid
    @13
    eqid
    wtru
    @18
    eqidd
    @18
    @0
    cbs
    cfv
    wceq
    wtru
    @18
    cC
    cO
    oppcbas.1
    @24
    2oppcbas
    a1i
    cC
    chomf
    cfv
    @0
    chomf
    cfv
    wceq
    wtru
    cC
    cO
    oppcbas.1
    2oppchomf
    a1i
    comfeq
    mpbird
    trud
end
