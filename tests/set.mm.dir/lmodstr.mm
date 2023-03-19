include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "c1.mm"
include "c6.mm"
include "cstr.mm"
include "c5.mm"
include "c2.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt2.mm"
include "2nn.mm"
include "plusgndx.mm"
include "2lt5.mm"
include "5nn.mm"
include "scandx.mm"
include "strle3.mm"
include "6nn.mm"
include "vscandx.mm"
include "strle1.mm"
include "5lt6.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem lmodstr
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cW: class W
  assume lvecfn.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , F >. } u. { <. ( .s ` ndx ) , .x. >. } )


  assert |- W Struct <. 1 , 6 >.

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
    csca
    cfv
    #
    cF
    cop
    ctp
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    csn
    #
    cun
    c1
    c6
    cop
    cstr
    lvecfn.w
    c1
    c5
    c6
    c6
    @3
    @5
    @0
    @1
    @2
    c1
    c2
    c5
    cB
    c.pl
    cF
    1nn
    basendx
    1lt2
    2nn
    plusgndx
    2lt5
    5nn
    scandx
    strle3
    @4
    c6
    c.x
    6nn
    vscandx
    strle1
    5lt6
    strleun
    eqbrtri
end
