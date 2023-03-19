include "ctopn.mm"
include "cfv.mm"
include "cts.mm"
include "cbs.mm"
include "crest.mm"
include "co.mm"
include "eqid.mm"
include "topnval.mm"
include "mgpbas.mm"
include "mgptset.mm"
include "3eqtr2i.mm"

theorem mgptopn
  let cR: class R
  let cJ: class J
  let cM: class M
  assume mgpbas.1: |- M = ( mulGrp ` R )
  assume mgptopn.2: |- J = ( TopOpen ` R )


  assert |- J = ( TopOpen ` M )

  proof
    cJ
    cR
    ctopn
    cfv
    cR
    cts
    cfv
    #
    cR
    cbs
    cfv
    #
    crest
    co
    cM
    ctopn
    cfv
    mgptopn.2
    @1
    @0
    cR
    @1
    eqid
    #
    @0
    eqid
    topnval
    @1
    @0
    cM
    @1
    cR
    cM
    mgpbas.1
    @2
    mgpbas
    cR
    cM
    mgpbas.1
    mgptset
    topnval
    3eqtr2i
end
