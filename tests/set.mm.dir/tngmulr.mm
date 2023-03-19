include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "3lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngmulr
  let cT: class T
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngmulr.2: |- .x. = ( .r ` G )


  assert |- ( N e. V -> .x. = ( .r ` T ) )

  proof
    cN
    cV
    wcel
    c.x
    cG
    cmulr
    cfv
    cT
    cmulr
    cfv
    tngmulr.2
    cT
    cmulr
    cG
    c3
    cN
    cV
    tngbas.t
    df-mulr
    3nn
    3lt9
    tnglem
    syl5eq
end
