include "cds.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "c6.mm"
include "2nn0.mm"
include "6nn.mm"
include "2lt6.mm"
include "declt.mm"
include "ttglem.mm"
include "eqtri.mm"

theorem ttgds
  let cD: class D
  let cG: class G
  let cH: class H
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgds.1: |- D = ( dist ` H )


  assert |- D = ( dist ` G )

  proof
    cD
    cH
    cds
    cfv
    cG
    cds
    cfv
    ttgds.1
    cds
    cG
    cH
    c1
    c2
    cdc
    ttgval.n
    df-ds
    c1
    c2
    1nn0
    2nn
    decnncl
    c1
    c2
    c6
    1nn0
    2nn0
    6nn
    2lt6
    declt
    ttglem
    eqtri
end
