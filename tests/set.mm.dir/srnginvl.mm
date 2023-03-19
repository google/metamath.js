include "cstv.mm"
include "c1.mm"
include "c4.mm"
include "cop.mm"
include "srngfn.mm"
include "starvid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem srnginvl
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  let cX: class X
  assume srngfn.r: |- R = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( *r ` ndx ) , .* >. } )


  assert |- ( .* e. X -> .* = ( *r ` R ) )

  proof
    c.as
    cR
    cstv
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
    starvid
    cnx
    cstv
    cfv
    c.as
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
    cmulr
    cfv
    c.x
    cop
    ctp
    #
    @0
    cun
    cR
    @0
    @1
    ssun2
    srngfn.r
    sseqtr4i
    strfv
end
