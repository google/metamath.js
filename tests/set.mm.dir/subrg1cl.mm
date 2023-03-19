include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "eqid.mm"
include "issubrg.mm"
include "simprbi.mm"
include "simprd.mm"

theorem subrg1cl
  let cA: class A
  let cR: class R
  let c.1: class .1.
  assume subrg1cl.a: |- .1. = ( 1r ` R )


  assert |- ( A e. ( SubRing ` R ) -> .1. e. A )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    wss
    #
    c.1
    cA
    wcel
    #
    @0
    cR
    crg
    wcel
    cR
    cA
    cress
    co
    crg
    wcel
    wa
    @2
    @3
    wa
    cA
    @1
    cR
    c.1
    @1
    eqid
    subrg1cl.a
    issubrg
    simprbi
    simprd
end
