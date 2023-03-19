include "cplusg.mm"
include "c1.mm"
include "c4.mm"
include "cop.mm"
include "srngfn.mm"
include "plusgid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cmulr.mm"
include "ctp.mm"
include "snsstp2.mm"
include "cstv.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"

theorem srngplusg
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  let cX: class X
  assume srngfn.r: |- R = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( *r ` ndx ) , .* >. } )


  assert |- ( .+ e. X -> .+ = ( +g ` R ) )

  proof
    c.pl
    cR
    cplusg
    cX
    c1
    c4
    cop
    cB
    c.pl
    cR
    c.x
    c.as
    srngfn.r
    srngfn
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
    cmulr
    cfv
    c.x
    cop
    #
    ctp
    #
    cR
    @1
    @0
    @2
    snsstp2
    @3
    @3
    cnx
    cstv
    cfv
    c.as
    cop
    csn
    #
    cun
    cR
    @3
    @4
    ssun1
    srngfn.r
    sseqtr4i
    sstri
    strfv
end
