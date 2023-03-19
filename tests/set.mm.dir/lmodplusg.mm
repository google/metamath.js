include "cplusg.mm"
include "c1.mm"
include "c6.mm"
include "cop.mm"
include "lmodstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "csca.mm"
include "ctp.mm"
include "snsstp2.mm"
include "cvsca.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem lmodplusg
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cW: class W
  let cX: class X
  assume lvecfn.w: |- W = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , F >. } u. { <. ( .s ` ndx ) , .x. >. } )


  assert |- ( .+ e. X -> .+ = ( +g ` W ) )

  proof
    c.pl
    cW
    cplusg
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
    plusgid
    cnx
    cplusg
    cfv
    c.pl
    cop
    #
    csn
    cnx
    cbs
    cfv
    cB
    cop
    #
    @0
    cnx
    csca
    cfv
    cF
    cop
    #
    ctp
    #
    cW
    @1
    @0
    @2
    snsstp2
    @3
    @3
    cnx
    cvsca
    cfv
    c.x
    cop
    csn
    #
    cun
    cW
    @3
    @4
    ssun1
    lvecfn.w
    sseqtr4i
    sstri
    strfv
end
