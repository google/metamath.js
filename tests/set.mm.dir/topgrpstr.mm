include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cts.mm"
include "ctp.mm"
include "c1.mm"
include "c9.mm"
include "cstr.mm"
include "c2.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt2.mm"
include "2nn.mm"
include "plusgndx.mm"
include "2lt9.mm"
include "9nn.mm"
include "tsetndx.mm"
include "strle3.mm"
include "eqbrtri.mm"

theorem topgrpstr
  let cB: class B
  let c.pl: class .+
  let cJ: class J
  let cW: class W
  assume topgrpfn.w: |- W = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. }


  assert |- W Struct <. 1 , 9 >.

  proof
    cW
    cnx
    cbs
    cfv
    #
    cB
    cop
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    cnx
    cts
    cfv
    #
    cJ
    cop
    ctp
    c1
    c9
    cop
    cstr
    topgrpfn.w
    @0
    @1
    @2
    c1
    c2
    c9
    cB
    c.pl
    cJ
    1nn
    basendx
    1lt2
    2nn
    plusgndx
    2lt9
    9nn
    tsetndx
    strle3
    eqbrtri
end
