include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "simpl3l.mm"
include "necomd.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simpl22.mm"
include "atcvr2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "breq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3r.mm"
include "atcvrj1.mm"
include "syl112anc.mm"
include "pm2.61dane.mm"
include "3expia.mm"
include "cp0.mm"
include "cfv.mm"
include "cal.mm"
include "hlatl.mm"
include "ad2antrr.mm"
include "simplr1.mm"
include "eqid.mm"
include "atn0.mm"
include "syl2anc.mm"
include "cbs.mm"
include "simpll.mm"
include "atbase.mm"
include "syl.mm"
include "simplr2.mm"
include "simplr3.mm"
include "atcvrj0.mm"
include "syl131anc.mm"
include "necon3bid.mm"
include "clat.mm"
include "hllat.mm"
include "latjcl.mm"
include "3jca.mm"
include "cvrle.mm"
include "sylancom.mm"
include "jca.mm"
include "ex.mm"
include "impbid.mm"

theorem atcvrj2b
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume atcvrj1x.l: |- .<_ = ( le ` K )
  assume atcvrj1x.j: |- .\/ = ( join ` K )
  assume atcvrj1x.c: |- C = ( <o ` K )
  assume atcvrj1x.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( ( Q =/= R /\ P .<_ ( Q .\/ R ) ) <-> P C ( Q .\/ R ) ) )

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
    cQ
    cR
    wne
    #
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    cP
    @7
    cC
    wbr
    #
    @0
    @4
    @9
    @10
    @0
    @4
    @9
    w3a
    #
    @10
    cP
    cR
    @11
    cP
    cR
    wceq
    #
    wa
    #
    @10
    cR
    @7
    cC
    wbr
    #
    @13
    cR
    cQ
    wne
    #
    @14
    @13
    cQ
    cR
    @6
    @8
    @0
    @4
    @12
    simpl3l
    necomd
    @13
    @0
    @3
    @2
    @15
    @14
    wb
    @0
    @4
    @9
    @12
    simpl1
    @1
    @2
    @3
    @0
    @9
    @12
    simpl23
    @1
    @2
    @3
    @0
    @9
    @12
    simpl22
    cA
    cC
    cR
    cQ
    c.or
    cK
    atcvrj1x.j
    atcvrj1x.c
    atcvrj1x.a
    atcvr2
    syl3anc
    mpbid
    @12
    @10
    @14
    wb
    @11
    cP
    cR
    @7
    cC
    breq1
    adantl
    mpbird
    @11
    cP
    cR
    wne
    #
    wa
    @0
    @4
    @16
    @8
    @10
    @0
    @4
    @9
    @16
    simpl1
    @0
    @4
    @9
    @16
    simpl2
    @11
    @16
    simpr
    @6
    @8
    @0
    @4
    @16
    simpl3r
    cA
    cC
    cP
    cQ
    cR
    c.or
    cK
    c.le
    atcvrj1x.l
    atcvrj1x.j
    atcvrj1x.c
    atcvrj1x.a
    atcvrj1
    syl112anc
    pm2.61dane
    3expia
    @5
    @10
    @9
    @5
    @10
    wa
    #
    @6
    @8
    @17
    cP
    cK
    cp0
    cfv
    #
    wne
    #
    @6
    @17
    cK
    cal
    wcel
    #
    @1
    @19
    @0
    @20
    @4
    @10
    cK
    hlatl
    ad2antrr
    @1
    @2
    @3
    @0
    @10
    simplr1
    #
    cA
    cP
    cK
    @18
    @18
    eqid
    #
    atcvrj1x.a
    atn0
    syl2anc
    @17
    cP
    @18
    cQ
    cR
    @17
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @3
    @10
    cP
    @18
    wceq
    cQ
    cR
    wceq
    wb
    @0
    @4
    @10
    simpll
    #
    @17
    @1
    @24
    @21
    cA
    @23
    cP
    cK
    @23
    eqid
    #
    atcvrj1x.a
    atbase
    syl
    #
    @1
    @2
    @3
    @0
    @10
    simplr2
    #
    @1
    @2
    @3
    @0
    @10
    simplr3
    #
    @5
    @10
    simpr
    cA
    @23
    cC
    cQ
    cR
    c.or
    cK
    cP
    @18
    @26
    atcvrj1x.j
    @22
    atcvrj1x.c
    atcvrj1x.a
    atcvrj0
    syl131anc
    necon3bid
    mpbid
    @5
    @10
    @0
    @24
    @7
    @23
    wcel
    #
    w3a
    @8
    @17
    @0
    @24
    @30
    @25
    @27
    @17
    cK
    clat
    wcel
    #
    cQ
    @23
    wcel
    #
    cR
    @23
    wcel
    #
    @30
    @0
    @31
    @4
    @10
    cK
    hllat
    ad2antrr
    @17
    @2
    @32
    @28
    cA
    @23
    cQ
    cK
    @26
    atcvrj1x.a
    atbase
    syl
    @17
    @3
    @33
    @29
    cA
    @23
    cR
    cK
    @26
    atcvrj1x.a
    atbase
    syl
    @23
    c.or
    cK
    cQ
    cR
    @26
    atcvrj1x.j
    latjcl
    syl3anc
    3jca
    chlt
    @23
    cC
    cK
    c.le
    cP
    @7
    @26
    atcvrj1x.l
    atcvrj1x.c
    cvrle
    sylancom
    jca
    ex
    impbid
end
