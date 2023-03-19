include "cvsca.mm"
include "c1.mm"
include "c6.mm"
include "cop.mm"
include "lmodstr.mm"
include "vscaid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem lmodvsca
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cW: class W
  let cX: class X
  assume lvecfn.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , F >. } u. { <. ( .s ` ndx ) , .x. >. } )


  assert |- ( .x. e. X -> .x. = ( .s ` W ) )

  proof
    c.x
    cW
    cvsca
    cX
    c1
    c6
    cop
    cB
    c.pl
    c.x
    cF
    cW
    lvecfn.w
    lmodstr
    vscaid
    cnx
    cvsca
    cfv
    c.x
    cop
    csn
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    c.pl
    cop
    cnx
    csca
    cfv
    cF
    cop
    ctp
    #
    @0
    cun
    cW
    @0
    @1
    ssun2
    lvecfn.w
    sseqtr4i
    strfv
end
