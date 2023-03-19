include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cminmar1.mm"
include "co.mm"
include "cfv.mm"
include "cur.mm"
include "cmarrep.mm"
include "wceq.mm"
include "eqid.mm"
include "minmar1marrep.mm"
include "adantr.mm"
include "oveqd.mm"
include "cbs.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr.mm"
include "ringidcl.mm"
include "3jca.mm"
include "marrepcl.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem minmar1cl
  let cA: class A
  let cB: class B
  let cR: class R
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume minmar1cl.a: |- A = ( N Mat R )
  assume minmar1cl.b: |- B = ( Base ` A )


  assert |- ( ( ( R e. Ring /\ M e. B ) /\ ( K e. N /\ L e. N ) ) -> ( K ( ( N minMatR1 R ) ` M ) L ) e. B )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cK
    cN
    wcel
    cL
    cN
    wcel
    wa
    #
    wa
    #
    cK
    cL
    cM
    cN
    cR
    cminmar1
    co
    cfv
    #
    co
    cK
    cL
    cM
    cR
    cur
    cfv
    #
    cN
    cR
    cmarrep
    co
    #
    co
    #
    co
    #
    cB
    @4
    @5
    @8
    cK
    cL
    @2
    @5
    @8
    wceq
    @3
    cA
    cB
    @7
    cR
    @6
    cM
    cN
    minmar1cl.a
    minmar1cl.b
    @7
    eqid
    @6
    eqid
    #
    minmar1marrep
    adantr
    oveqd
    @2
    @0
    @1
    @6
    cR
    cbs
    cfv
    #
    wcel
    #
    w3a
    @3
    @9
    cB
    wcel
    @2
    @0
    @1
    @12
    @0
    @1
    simpl
    @0
    @1
    simpr
    @0
    @12
    @1
    @11
    cR
    @6
    @11
    eqid
    @10
    ringidcl
    adantr
    3jca
    cA
    cB
    cR
    @6
    cK
    cL
    cM
    cN
    minmar1cl.a
    minmar1cl.b
    marrepcl
    sylan
    eqeltrd
end
