include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "simpr3.mm"
include "hlatjidm.mm"
include "syldan.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "cal.mm"
include "wn.mm"
include "hlatl.mm"
include "adantr.mm"
include "simpr1.mm"
include "atnlt.mm"
include "syl3anc.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "wne.mm"
include "cple.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl.mm"
include "clat.mm"
include "hllat.mm"
include "simpr2.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "pltle.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "anassrs.mm"
include "atcvrj2.mm"
include "ex.mm"
include "syld.mm"
include "pm2.61dane.mm"
include "cvrlt.mm"
include "impbid.mm"

theorem atltcvr
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  assume atltcvr.s: |- .< = ( lt ` K )
  assume atltcvr.j: |- .\/ = ( join ` K )
  assume atltcvr.a: |- A = ( Atoms ` K )
  assume atltcvr.c: |- C = ( <o ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( P .< ( Q .\/ R ) <-> P C ( Q .\/ R ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
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
    cP
    cQ
    cR
    c.or
    co
    #
    c.lt
    wbr
    #
    cP
    @6
    cC
    wbr
    #
    @5
    @7
    @8
    wi
    cQ
    cR
    @5
    cQ
    cR
    wceq
    #
    wa
    #
    @7
    cP
    cR
    c.lt
    wbr
    #
    @8
    @10
    @6
    cR
    cP
    c.lt
    @9
    @5
    @6
    cR
    cR
    c.or
    co
    #
    cR
    cQ
    cR
    cR
    c.or
    oveq1
    @0
    @4
    @3
    @12
    cR
    wceq
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    c.or
    cK
    cR
    atltcvr.j
    atltcvr.a
    hlatjidm
    syldan
    sylan9eqr
    breq2d
    @5
    @11
    @8
    wi
    @9
    @5
    @11
    @8
    @5
    cK
    cal
    wcel
    #
    @1
    @3
    @11
    wn
    @0
    @14
    @4
    cK
    hlatl
    adantr
    @0
    @1
    @2
    @3
    simpr1
    #
    @13
    cA
    cP
    cR
    c.lt
    cK
    atltcvr.s
    atltcvr.a
    atnlt
    syl3anc
    pm2.21d
    adantr
    sylbid
    @5
    cQ
    cR
    wne
    #
    wa
    #
    @7
    cP
    @6
    cK
    cple
    cfv
    #
    wbr
    #
    @8
    @5
    @7
    @19
    wi
    #
    @16
    @5
    @0
    @1
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @20
    @0
    @4
    simpl
    #
    @15
    @5
    cK
    clat
    wcel
    #
    cQ
    @21
    wcel
    #
    cR
    @21
    wcel
    #
    @22
    @0
    @24
    @4
    cK
    hllat
    adantr
    @5
    @2
    @25
    @0
    @1
    @2
    @3
    simpr2
    cA
    @21
    cQ
    cK
    @21
    eqid
    #
    atltcvr.a
    atbase
    syl
    @5
    @3
    @26
    @13
    cA
    @21
    cR
    cK
    @27
    atltcvr.a
    atbase
    syl
    @21
    c.or
    cK
    cQ
    cR
    @27
    atltcvr.j
    latjcl
    syl3anc
    #
    chlt
    cA
    @21
    c.lt
    cK
    @18
    cP
    @6
    @18
    eqid
    #
    atltcvr.s
    pltle
    syl3anc
    adantr
    @17
    @19
    @8
    @17
    @19
    wa
    @0
    @4
    @16
    @19
    wa
    #
    w3a
    #
    @8
    @5
    @16
    @19
    @31
    @5
    @30
    wa
    @0
    @4
    @30
    @0
    @4
    @30
    simpll
    @0
    @4
    @30
    simplr
    @5
    @30
    simpr
    3jca
    anassrs
    cA
    cC
    cP
    cQ
    cR
    c.or
    cK
    @18
    @29
    atltcvr.j
    atltcvr.c
    atltcvr.a
    atcvrj2
    syl
    ex
    syld
    pm2.61dane
    @5
    @0
    cP
    @21
    wcel
    #
    @22
    @8
    @7
    wi
    @23
    @5
    @1
    @32
    @15
    cA
    @21
    cP
    cK
    @27
    atltcvr.a
    atbase
    syl
    @28
    @0
    @32
    @22
    w3a
    @8
    @7
    chlt
    @21
    cC
    c.lt
    cK
    cP
    @6
    @27
    atltcvr.s
    atltcvr.c
    cvrlt
    ex
    syl3anc
    impbid
end
