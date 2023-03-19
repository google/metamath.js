include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cds.mm"
include "citv.mm"
include "ctp.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "cstr.mm"
include "c2.mm"
include "1nn.mm"
include "basendx.mm"
include "2nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "2nn.mm"
include "decnncl.mm"
include "dsndx.mm"
include "6nn.mm"
include "2lt6.mm"
include "declt.mm"
include "itvndx.mm"
include "strle3.mm"
include "eqbrtri.mm"

theorem trkgstr
  let cD: class D
  let cU: class U
  let cI: class I
  let cW: class W
  assume trkgstr.w: |- W = { <. ( Base ` ndx ) , U >. , <. ( dist ` ndx ) , D >. , <. ( Itv ` ndx ) , I >. }


  assert |- W Struct <. 1 , ; 1 6 >.

  proof
    cW
    cnx
    cbs
    cfv
    #
    cU
    cop
    cnx
    cds
    cfv
    #
    cD
    cop
    cnx
    citv
    cfv
    #
    cI
    cop
    ctp
    c1
    c1
    c6
    cdc
    #
    cop
    cstr
    trkgstr.w
    @0
    @1
    @2
    c1
    c1
    c2
    cdc
    @3
    cU
    cD
    cI
    1nn
    basendx
    c1
    c2
    c1
    1nn
    2nn0
    1nn0
    1lt10
    declti
    c1
    c2
    1nn0
    2nn
    decnncl
    dsndx
    c1
    c2
    c6
    1nn0
    2nn0
    6nn
    2lt6
    declt
    c1
    c6
    1nn0
    6nn
    decnncl
    itvndx
    strle3
    eqbrtri
end
