include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "lidlss.mm"
include "ad2antlr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "ringridm.mm"
include "ad2ant2rl.mm"
include "lidlmcl.mm"
include "ancom2s.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ex.mm"
include "ringidcl.mm"
include "adantr.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem lidl1el
  let cB: class B
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidlcl.b: |- B = ( Base ` R )
  assume lidl1el.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ I e. U ) -> ( .1. e. I <-> I = B ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    c.1
    cI
    wcel
    #
    cI
    cB
    wceq
    #
    @2
    @3
    @4
    @2
    @3
    wa
    #
    cI
    cB
    @1
    cI
    cB
    wss
    @0
    @3
    cB
    cI
    cU
    cR
    lidlcl.b
    lidlcl.u
    lidlss
    ad2antlr
    @5
    va
    cB
    cI
    @2
    @3
    va
    cv
    #
    cB
    wcel
    #
    @6
    cI
    wcel
    @2
    @3
    @7
    wa
    wa
    @6
    c.1
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    cI
    @0
    @7
    @9
    @6
    wceq
    @1
    @3
    cB
    cR
    @8
    c.1
    @6
    lidlcl.b
    @8
    eqid
    #
    lidl1el.o
    ringridm
    ad2ant2rl
    @2
    @7
    @3
    @9
    cI
    wcel
    cB
    cR
    @8
    cU
    cI
    @6
    c.1
    lidlcl.u
    lidlcl.b
    @10
    lidlmcl
    ancom2s
    eqeltrrd
    expr
    ssrdv
    eqssd
    ex
    @2
    @3
    @4
    c.1
    cB
    wcel
    #
    @0
    @11
    @1
    cB
    cR
    c.1
    lidlcl.b
    lidl1el.o
    ringidcl
    adantr
    cI
    cB
    c.1
    eleq2
    syl5ibrcom
    impbid
end
