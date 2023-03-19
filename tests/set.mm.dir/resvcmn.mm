include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "eqid.mm"
include "resvbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "resvplusg.mm"
include "oveqdr.mm"
include "cmnpropd.mm"

theorem resvcmn
  let cA: class A
  let cG: class G
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume resvbas.1: |- H = ( G |`v A )


  assert |- ( A e. V -> ( G e. CMnd <-> H e. CMnd ) )

  proof
    cA
    cV
    wcel
    #
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cH
    @0
    @1
    eqidd
    cA
    @1
    cG
    cH
    cV
    resvbas.1
    @1
    eqid
    resvbas
    @0
    vx
    cv
    @1
    wcel
    vy
    cv
    @1
    wcel
    wa
    vx
    vy
    cG
    cplusg
    cfv
    #
    cH
    cplusg
    cfv
    cA
    @2
    cG
    cH
    cV
    resvbas.1
    @2
    eqid
    resvplusg
    oveqdr
    cmnpropd
end
