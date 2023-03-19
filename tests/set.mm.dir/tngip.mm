include "wcel.mm"
include "cip.mm"
include "cfv.mm"
include "c8.mm"
include "df-ip.mm"
include "8nn.mm"
include "8lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngip
  let cT: class T
  let cG: class G
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngip.2: |- ., = ( .i ` G )


  assert |- ( N e. V -> ., = ( .i ` T ) )

  proof
    cN
    cV
    wcel
    c.xi
    cG
    cip
    cfv
    cT
    cip
    cfv
    tngip.2
    cT
    cip
    cG
    c8
    cN
    cV
    tngbas.t
    df-ip
    8nn
    8lt9
    tnglem
    syl5eq
end
