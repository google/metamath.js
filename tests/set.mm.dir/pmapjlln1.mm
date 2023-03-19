include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wceq.mm"
include "simpl.mm"
include "pmapssat.mm"
include "3ad2antr1.mm"
include "simpr2.mm"
include "atbase.mm"
include "syl.mm"
include "syldan.mm"
include "simpr3.mm"
include "paddass.mm"
include "syl13anc.mm"
include "clat.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr1.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapjat1.mm"
include "latjass.mm"
include "fveq2d.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem pmapjlln1
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pmapjat.b: |- B = ( Base ` K )
  assume pmapjat.j: |- .\/ = ( join ` K )
  assume pmapjat.a: |- A = ( Atoms ` K )
  assume pmapjat.m: |- M = ( pmap ` K )
  assume pmapjat.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ Q e. A /\ R e. A ) ) -> ( M ` ( X .\/ ( Q .\/ R ) ) ) = ( ( M ` X ) .+ ( M ` ( Q .\/ R ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cM
    cfv
    #
    cQ
    cM
    cfv
    #
    c.pl
    co
    #
    cR
    cM
    cfv
    #
    c.pl
    co
    #
    @6
    @7
    @9
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cQ
    cR
    c.or
    co
    #
    c.or
    co
    #
    cM
    cfv
    #
    @6
    @13
    cM
    cfv
    #
    c.pl
    co
    @5
    @0
    @6
    cA
    wss
    #
    @7
    cA
    wss
    #
    @9
    cA
    wss
    #
    @10
    @12
    wceq
    @0
    @4
    simpl
    #
    @0
    @2
    @1
    @17
    @3
    cA
    cB
    chlt
    cK
    cM
    cX
    pmapjat.b
    pmapjat.a
    pmapjat.m
    pmapssat
    3ad2antr1
    @0
    @4
    cQ
    cB
    wcel
    #
    @18
    @5
    @2
    @21
    @0
    @1
    @2
    @3
    simpr2
    cA
    cB
    cQ
    cK
    pmapjat.b
    pmapjat.a
    atbase
    syl
    #
    cA
    cB
    chlt
    cK
    cM
    cQ
    pmapjat.b
    pmapjat.a
    pmapjat.m
    pmapssat
    syldan
    @0
    @4
    cR
    cB
    wcel
    #
    @19
    @5
    @3
    @23
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    cB
    cR
    cK
    pmapjat.b
    pmapjat.a
    atbase
    syl
    #
    cA
    cB
    chlt
    cK
    cM
    cR
    pmapjat.b
    pmapjat.a
    pmapjat.m
    pmapssat
    syldan
    cA
    c.pl
    cK
    @6
    @7
    @9
    pmapjat.a
    pmapjat.p
    paddass
    syl13anc
    @5
    cX
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    cM
    cfv
    #
    @26
    cM
    cfv
    #
    @9
    c.pl
    co
    #
    @15
    @10
    @5
    @0
    @26
    cB
    wcel
    #
    @3
    @28
    @30
    wceq
    @20
    @5
    cK
    clat
    wcel
    #
    @1
    @21
    @31
    @0
    @32
    @4
    cK
    hllat
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @22
    cB
    c.or
    cK
    cX
    cQ
    pmapjat.b
    pmapjat.j
    latjcl
    syl3anc
    @24
    cA
    cB
    c.pl
    cR
    c.or
    cK
    cM
    @26
    pmapjat.b
    pmapjat.j
    pmapjat.a
    pmapjat.m
    pmapjat.p
    pmapjat1
    syl3anc
    @5
    @27
    @14
    cM
    @5
    @32
    @1
    @21
    @23
    @27
    @14
    wceq
    @33
    @34
    @22
    @25
    cB
    c.or
    cK
    cX
    cQ
    cR
    pmapjat.b
    pmapjat.j
    latjass
    syl13anc
    fveq2d
    @5
    @29
    @8
    @9
    c.pl
    @0
    @1
    @2
    @29
    @8
    wceq
    @3
    cA
    cB
    c.pl
    cQ
    c.or
    cK
    cM
    cX
    pmapjat.b
    pmapjat.j
    pmapjat.a
    pmapjat.m
    pmapjat.p
    pmapjat1
    3adant3r3
    oveq1d
    3eqtr3d
    @5
    @16
    @11
    @6
    c.pl
    @5
    @0
    @21
    @3
    @16
    @11
    wceq
    @20
    @22
    @24
    cA
    cB
    c.pl
    cR
    c.or
    cK
    cM
    cQ
    pmapjat.b
    pmapjat.j
    pmapjat.a
    pmapjat.m
    pmapjat.p
    pmapjat1
    syl3anc
    oveq2d
    3eqtr4d
end
