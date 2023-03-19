include "ctgp.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "eqid.mm"
include "istgp.mm"
include "simp2bi.mm"

theorem tgptmd
  let cG: class G


  assert |- ( G e. TopGrp -> G e. TopMnd )

  proof
    cG
    ctgp
    wcel
    cG
    cgrp
    wcel
    cG
    ctmd
    wcel
    cG
    cminusg
    cfv
    #
    cG
    ctopn
    cfv
    #
    @1
    ccn
    co
    wcel
    cG
    @0
    @1
    @1
    eqid
    @0
    eqid
    istgp
    simp2bi
end
