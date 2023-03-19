include "wcel.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "cur.mm"
include "eqid.mm"
include "resvbas.mm"
include "eleq2d.mm"
include "resvmulr.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "iotabidv.mm"
include "dfur2.mm"
include "3eqtr4g.mm"

theorem resv1r
  let cA: class A
  let c.1: class .1.
  let cG: class G
  let cH: class H
  let cV: class V
  let ve: setvar e
  let vx: setvar x
  assume resvbas.1: |- H = ( G |`v A )
  assume resv1r.2: |- .1. = ( 1r ` G )


  assert |- ( A e. V -> .1. = ( 1r ` H ) )

  proof
    cA
    cV
    wcel
    #
    ve
    cv
    #
    cG
    cbs
    cfv
    #
    wcel
    #
    @1
    vx
    cv
    #
    cG
    cmulr
    cfv
    #
    co
    #
    @4
    wceq
    #
    @4
    @1
    @5
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    @2
    wral
    #
    wa
    #
    ve
    cio
    @1
    cH
    cbs
    cfv
    #
    wcel
    #
    @1
    @4
    cH
    cmulr
    cfv
    #
    co
    #
    @4
    wceq
    #
    @4
    @1
    @15
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    @13
    wral
    #
    wa
    #
    ve
    cio
    c.1
    cH
    cur
    cfv
    #
    @0
    @12
    @22
    ve
    @0
    @3
    @14
    @11
    @21
    @0
    @2
    @13
    @1
    cA
    @2
    cG
    cH
    cV
    resvbas.1
    @2
    eqid
    #
    resvbas
    #
    eleq2d
    @0
    @10
    @20
    vx
    @2
    @13
    @25
    @0
    @7
    @17
    @9
    @19
    @0
    @6
    @16
    @4
    @0
    @5
    @15
    @1
    @4
    cA
    @5
    cG
    cH
    cV
    resvbas.1
    @5
    eqid
    #
    resvmulr
    #
    oveqd
    eqeq1d
    @0
    @8
    @18
    @4
    @0
    @5
    @15
    @4
    @1
    @27
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    anbi12d
    iotabidv
    vx
    @2
    cG
    @5
    c.1
    ve
    @24
    @26
    resv1r.2
    dfur2
    vx
    @13
    cH
    @15
    @23
    ve
    @13
    eqid
    @15
    eqid
    @23
    eqid
    dfur2
    3eqtr4g
end
