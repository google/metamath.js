include "wcel.mm"
include "cvsca.mm"
include "cfv.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "6lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngvsca
  let cT: class T
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngvsca.2: |- .x. = ( .s ` G )


  assert |- ( N e. V -> .x. = ( .s ` T ) )

  proof
    cN
    cV
    wcel
    c.x
    cG
    cvsca
    cfv
    cT
    cvsca
    cfv
    tngvsca.2
    cT
    cvsca
    cG
    c6
    cN
    cV
    tngbas.t
    df-vsca
    6nn
    6lt9
    tnglem
    syl5eq
end
