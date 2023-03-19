include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngbas
  let cB: class B
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngbas.2: |- B = ( Base ` G )


  assert |- ( N e. V -> B = ( Base ` T ) )

  proof
    cN
    cV
    wcel
    cB
    cG
    cbs
    cfv
    cT
    cbs
    cfv
    tngbas.2
    cT
    cbs
    cG
    c1
    cN
    cV
    tngbas.t
    df-base
    1nn
    1lt9
    tnglem
    syl5eq
end
