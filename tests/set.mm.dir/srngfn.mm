include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cstv.mm"
include "csn.mm"
include "cun.mm"
include "c1.mm"
include "c4.mm"
include "cstr.mm"
include "c3.mm"
include "eqid.mm"
include "rngstr.mm"
include "4nn.mm"
include "starvndx.mm"
include "strle1.mm"
include "3lt4.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem srngfn
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  assume srngfn.r: |- R = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u. { <. ( *r ` ndx ) , .* >. } )


  assert |- R Struct <. 1 , 4 >.

  proof
    cR
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
    cnx
    cstv
    cfv
    #
    c.as
    cop
    csn
    #
    cun
    c1
    c4
    cop
    cstr
    srngfn.r
    c1
    c3
    c4
    c4
    @0
    @2
    cB
    c.pl
    @0
    c.x
    @0
    eqid
    rngstr
    @1
    c4
    c.as
    4nn
    starvndx
    strle1
    3lt4
    strleun
    eqbrtri
end
