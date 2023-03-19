include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "tngbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "tngplusg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "syl5eq.mm"

theorem tng0
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tng0.2: |- .0. = ( 0g ` G )


  assert |- ( N e. V -> .0. = ( 0g ` T ) )

  proof
    cN
    cV
    wcel
    #
    c.0
    cG
    c0g
    cfv
    cT
    c0g
    cfv
    tng0.2
    @0
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cT
    @0
    @1
    eqidd
    @1
    cT
    cG
    cN
    cV
    tngbas.t
    @1
    eqid
    tngbas
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
    cT
    cplusg
    cfv
    @2
    cT
    cG
    cN
    cV
    tngbas.t
    @2
    eqid
    tngplusg
    oveqdr
    grpidpropd
    syl5eq
end
