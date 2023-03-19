include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "pmapjat1.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "wss.mm"
include "simp1.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "paddcom.mm"
include "3eqtr4d.mm"

theorem pmapjat2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
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


  assert |- ( ( K e. HL /\ X e. B /\ Q e. A ) -> ( M ` ( Q .\/ X ) ) = ( ( M ` Q ) .+ ( M ` X ) ) )

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
    w3a
    #
    cX
    cQ
    c.or
    co
    #
    cM
    cfv
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
    cQ
    cX
    c.or
    co
    #
    cM
    cfv
    @6
    @5
    c.pl
    co
    #
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
    @3
    @8
    @4
    cM
    @3
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @1
    @8
    @4
    wceq
    @0
    @1
    @10
    @2
    cK
    hllat
    3ad2ant1
    #
    @2
    @0
    @11
    @1
    cA
    cB
    cQ
    cK
    pmapjat.b
    pmapjat.a
    atbase
    3ad2ant3
    #
    @0
    @1
    @2
    simp2
    cB
    c.or
    cK
    cQ
    cX
    pmapjat.b
    pmapjat.j
    latjcom
    syl3anc
    fveq2d
    @3
    @10
    @6
    cA
    wss
    #
    @5
    cA
    wss
    #
    @9
    @7
    wceq
    @12
    @3
    @0
    @11
    @14
    @0
    @1
    @2
    simp1
    @13
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
    syl2anc
    @0
    @1
    @15
    @2
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
    3adant3
    cA
    c.pl
    cK
    @6
    @5
    pmapjat.a
    pmapjat.p
    paddcom
    syl3anc
    3eqtr4d
end
