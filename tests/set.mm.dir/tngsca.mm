include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "5lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngsca
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngsca.2: |- F = ( Scalar ` G )


  assert |- ( N e. V -> F = ( Scalar ` T ) )

  proof
    cN
    cV
    wcel
    cF
    cG
    csca
    cfv
    cT
    csca
    cfv
    tngsca.2
    cT
    csca
    cG
    c5
    cN
    cV
    tngbas.t
    df-sca
    5nn
    5lt9
    tnglem
    syl5eq
end
