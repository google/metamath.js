include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cmgm.mm"
include "prex.mm"
include "0ex.mm"
include "eqid.mm"
include "grpbase.mm"
include "eqcomd.mm"
include "ax-mp.mm"
include "mgm0.mm"
include "mp2an.mm"

theorem mgm0b
  let cO: class O


  assert |- { <. ( Base ` ndx ) , (/) >. , <. ( +g ` ndx ) , O >. } e. Mgm

  proof
    cnx
    cbs
    cfv
    c0
    cop
    #
    cnx
    cplusg
    cfv
    cO
    cop
    #
    cpr
    #
    cvv
    wcel
    @2
    cbs
    cfv
    #
    c0
    wceq
    #
    @2
    cmgm
    wcel
    @0
    @1
    prex
    c0
    cvv
    wcel
    #
    @4
    0ex
    @5
    c0
    @3
    c0
    cO
    @2
    cvv
    @2
    eqid
    grpbase
    eqcomd
    ax-mp
    @2
    cvv
    mgm0
    mp2an
end
