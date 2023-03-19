include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt9.mm"
include "tnglem.mm"
include "syl5eq.mm"

theorem tngplusg
  let c.pl: class .+
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngplusg.2: |- .+ = ( +g ` G )


  assert |- ( N e. V -> .+ = ( +g ` T ) )

  proof
    cN
    cV
    wcel
    c.pl
    cG
    cplusg
    cfv
    cT
    cplusg
    cfv
    tngplusg.2
    cT
    cplusg
    cG
    c2
    cN
    cV
    tngbas.t
    df-plusg
    2nn
    2lt9
    tnglem
    syl5eq
end
