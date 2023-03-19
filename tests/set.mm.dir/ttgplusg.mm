include "cplusg.mm"
include "cfv.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "c1.mm"
include "c6.mm"
include "1nn.mm"
include "6nn0.mm"
include "2nn0.mm"
include "2lt10.mm"
include "declti.mm"
include "ttglem.mm"
include "eqtri.mm"

theorem ttgplusg
  let c.pl: class .+
  let cG: class G
  let cH: class H
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgplusg.1: |- .+ = ( +g ` H )


  assert |- .+ = ( +g ` G )

  proof
    c.pl
    cH
    cplusg
    cfv
    cG
    cplusg
    cfv
    ttgplusg.1
    cplusg
    cG
    cH
    c2
    ttgval.n
    df-plusg
    2nn
    c1
    c6
    c2
    1nn
    6nn0
    2nn0
    2lt10
    declti
    ttglem
    eqtri
end
