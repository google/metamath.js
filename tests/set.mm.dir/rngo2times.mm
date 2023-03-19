include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ringlidm.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "wceq.mm"
include "simpl.mm"
include "ringidcl.mm"
include "adantr.mm"
include "simpr.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "eqtr4d.mm"

theorem rngo2times
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vx: setvar x
  let cX: class X
  assume ringadd2.b: |- B = ( Base ` R )
  assume ringadd2.p: |- .+ = ( +g ` R )
  assume ringadd2.t: |- .x. = ( .r ` R )
  assume rngo2times.u: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ A e. B ) -> ( A .+ A ) = ( ( .1. .+ .1. ) .x. A ) )

  proof
    cR
    crg
    wcel
    #
    cA
    cB
    wcel
    #
    wa
    #
    cA
    cA
    c.pl
    co
    c.1
    cA
    c.x
    co
    #
    @3
    c.pl
    co
    #
    c.1
    c.1
    c.pl
    co
    cA
    c.x
    co
    #
    @2
    cA
    @3
    cA
    @3
    c.pl
    @2
    @3
    cA
    cB
    cR
    c.x
    c.1
    cA
    ringadd2.b
    ringadd2.t
    rngo2times.u
    ringlidm
    eqcomd
    #
    @6
    oveq12d
    @2
    @0
    c.1
    cB
    wcel
    #
    @7
    @1
    @5
    @4
    wceq
    @0
    @1
    simpl
    @0
    @7
    @1
    cB
    cR
    c.1
    ringadd2.b
    rngo2times.u
    ringidcl
    adantr
    #
    @8
    @0
    @1
    simpr
    cB
    c.pl
    cR
    c.x
    c.1
    c.1
    cA
    ringadd2.b
    ringadd2.p
    ringadd2.t
    ringdir
    syl13anc
    eqtr4d
end
