include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "cress.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "eqid.mm"
include "resstopn.mm"
include "tgioo2.mm"
include "crefld.mm"
include "df-refld.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem tgioo3
  let cJ: class J
  assume tgioo3.1: |- J = ( TopOpen ` RRfld )


  assert |- ( topGen ` ran (,) ) = J

  proof
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    ccnfld
    cr
    cress
    co
    #
    ctopn
    cfv
    #
    cioo
    crn
    ctg
    cfv
    cJ
    cr
    @1
    @0
    ccnfld
    @1
    eqid
    @0
    eqid
    #
    resstopn
    @0
    @3
    tgioo2
    cJ
    crefld
    ctopn
    cfv
    @2
    tgioo3.1
    crefld
    @1
    ctopn
    df-refld
    fveq2i
    eqtri
    3eqtr4i
end
