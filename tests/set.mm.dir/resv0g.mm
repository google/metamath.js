include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "resvbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "resvplusg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "syl5eq.mm"

theorem resv0g
  let cA: class A
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume resvbas.1: |- H = ( G |`v A )
  assume resv0g.2: |- .0. = ( 0g ` G )


  assert |- ( A e. V -> .0. = ( 0g ` H ) )

  proof
    cA
    cV
    wcel
    #
    c.0
    cG
    c0g
    cfv
    cH
    c0g
    cfv
    resv0g.2
    @0
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
    grpidpropd
    syl5eq
end
