include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "cp0.mm"
include "cfv.mm"
include "simpl1l.mm"
include "simpr.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "col.mm"
include "simp1l.mm"
include "hlol.mm"
include "syl.mm"
include "adantr.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "olj02.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "adantl.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "wo.mm"
include "simp21.mm"
include "simp1r.mm"
include "meetat2.mm"
include "mpjaodan.mm"

theorem atmod1i1m
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume atmod.b: |- B = ( Base ` K )
  assume atmod.l: |- .<_ = ( le ` K )
  assume atmod.j: |- .\/ = ( join ` K )
  assume atmod.m: |- ./\ = ( meet ` K )
  assume atmod.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A ) /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( X ./\ P ) .<_ Z ) -> ( ( X ./\ P ) .\/ ( Y ./\ Z ) ) = ( ( ( X ./\ P ) .\/ Y ) ./\ Z ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cP
    c.an
    co
    #
    cZ
    c.le
    wbr
    #
    w3a
    #
    @7
    cA
    wcel
    #
    @7
    cY
    cZ
    c.an
    co
    #
    c.or
    co
    #
    @7
    cY
    c.or
    co
    #
    cZ
    c.an
    co
    #
    wceq
    #
    @7
    cK
    cp0
    cfv
    #
    wceq
    #
    @9
    @10
    wa
    @0
    @10
    @4
    @5
    @8
    @15
    @0
    @1
    @6
    @8
    @10
    simpl1l
    @9
    @10
    simpr
    @3
    @4
    @5
    @2
    @8
    @10
    simpl22
    @3
    @4
    @5
    @2
    @8
    @10
    simpl23
    @2
    @6
    @8
    @10
    simpl3
    cA
    cB
    @7
    c.or
    cK
    c.le
    c.an
    cY
    cZ
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    atmod.a
    atmod1i1
    syl131anc
    @9
    @17
    wa
    #
    @16
    @11
    c.or
    co
    #
    @11
    @12
    @14
    @18
    cK
    col
    wcel
    #
    @11
    cB
    wcel
    #
    @19
    @11
    wceq
    @9
    @20
    @17
    @9
    @0
    @20
    @0
    @1
    @6
    @8
    simp1l
    #
    cK
    hlol
    syl
    #
    adantr
    #
    @18
    cK
    clat
    wcel
    #
    @4
    @5
    @21
    @9
    @25
    @17
    @9
    @0
    @25
    @22
    cK
    hllat
    syl
    adantr
    @3
    @4
    @5
    @2
    @8
    @17
    simpl22
    #
    @3
    @4
    @5
    @2
    @8
    @17
    simpl23
    cB
    cK
    c.an
    cY
    cZ
    atmod.b
    atmod.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    @11
    @16
    atmod.b
    atmod.j
    @16
    eqid
    #
    olj02
    syl2anc
    @17
    @12
    @19
    wceq
    @9
    @7
    @16
    @11
    c.or
    oveq1
    adantl
    @18
    @13
    cY
    cZ
    c.an
    @18
    @13
    @16
    cY
    c.or
    co
    #
    cY
    @17
    @13
    @28
    wceq
    @9
    @7
    @16
    cY
    c.or
    oveq1
    adantl
    @18
    @20
    @4
    @28
    cY
    wceq
    @24
    @26
    cB
    c.or
    cK
    cY
    @16
    atmod.b
    atmod.j
    @27
    olj02
    syl2anc
    eqtrd
    oveq1d
    3eqtr4d
    @9
    @20
    @3
    @1
    @10
    @17
    wo
    @23
    @2
    @3
    @4
    @5
    @8
    simp21
    @0
    @1
    @6
    @8
    simp1r
    cA
    cB
    cP
    cK
    c.an
    cX
    @16
    atmod.b
    atmod.m
    @27
    atmod.a
    meetat2
    syl3anc
    mpjaodan
end
