include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "c1.mm"
include "c3.mm"
include "cstr.mm"
include "c2.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt2.mm"
include "2nn.mm"
include "plusgndx.mm"
include "2lt3.mm"
include "3nn.mm"
include "mulrndx.mm"
include "strle3.mm"
include "eqbrtri.mm"

theorem rngstr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  assume rngfn.r: |- R = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. }


  assert |- R Struct <. 1 , 3 >.

  proof
    cR
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
    cmulr
    cfv
    #
    c.x
    cop
    ctp
    c1
    c3
    cop
    cstr
    rngfn.r
    @0
    @1
    @2
    c1
    c2
    c3
    cB
    c.pl
    c.x
    1nn
    basendx
    1lt2
    2nn
    plusgndx
    2lt3
    3nn
    mulrndx
    strle3
    eqbrtri
end
