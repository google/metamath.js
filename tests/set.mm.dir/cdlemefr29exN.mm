include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "wral.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp2r.mm"
include "lhpmcvr2.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "wi.mm"
include "clat.mm"
include "simp11l.mm"
include "adantr.mm"
include "hllat.mm"
include "syl.mm"
include "simpl3.mm"
include "simprl.mm"
include "rsp.mm"
include "sylc.mm"
include "simp2rl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "expr.mm"
include "adantrd.mm"
include "ancld.mm"
include "ex.mm"
include "reximdai.mm"
include "mpd.mm"

theorem cdlemefr29exN
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume cdlemefr29.b: |- B = ( Base ` K )
  assume cdlemefr29.l: |- .<_ = ( le ` K )
  assume cdlemefr29.j: |- .\/ = ( join ` K )
  assume cdlemefr29.m: |- ./\ = ( meet ` K )
  assume cdlemefr29.a: |- A = ( Atoms ` K )
  assume cdlemefr29.h: |- H = ( LHyp ` K )

  disjoint A s
  disjoint B s
  disjoint H s
  disjoint K s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint W s
  disjoint X s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) /\ A. s e. A C e. B ) -> E. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) /\ ( C .\/ ( X ./\ W ) ) e. B ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cC
    cB
    wcel
    #
    vs
    cA
    wral
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    #
    @18
    cC
    @16
    c.or
    co
    cB
    wcel
    #
    wa
    #
    vs
    cA
    wrex
    @13
    @2
    @9
    @19
    @2
    @3
    @4
    @10
    @12
    simp11
    @5
    @6
    @9
    @12
    simp2r
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vs
    cdlemefr29.b
    cdlemefr29.l
    cdlemefr29.j
    cdlemefr29.m
    cdlemefr29.a
    cdlemefr29.h
    lhpmcvr2
    syl2anc
    @13
    @18
    @21
    vs
    cA
    @5
    @10
    @12
    vs
    @5
    vs
    nfv
    @10
    vs
    nfv
    @11
    vs
    cA
    nfra1
    nf3an
    @13
    @14
    cA
    wcel
    #
    @18
    @21
    wi
    @13
    @22
    wa
    #
    @18
    @20
    @23
    @15
    @20
    @17
    @13
    @22
    @15
    @20
    @13
    @22
    @15
    wa
    #
    wa
    #
    cK
    clat
    wcel
    #
    @11
    @16
    cB
    wcel
    #
    @20
    @25
    @0
    @26
    @13
    @0
    @24
    @0
    @1
    @3
    @4
    @10
    @12
    simp11l
    #
    adantr
    cK
    hllat
    #
    syl
    @25
    @12
    @22
    @11
    @5
    @10
    @12
    @24
    simpl3
    @13
    @22
    @15
    simprl
    @11
    vs
    cA
    rsp
    sylc
    @13
    @27
    @24
    @13
    @26
    @7
    cW
    cB
    wcel
    #
    @27
    @13
    @0
    @26
    @28
    @29
    syl
    @7
    @8
    @6
    @5
    @12
    simp2rl
    @13
    @1
    @30
    @0
    @1
    @3
    @4
    @10
    @12
    simp11r
    cB
    cH
    cK
    cW
    cdlemefr29.b
    cdlemefr29.h
    lhpbase
    syl
    cB
    cK
    c.an
    cX
    cW
    cdlemefr29.b
    cdlemefr29.m
    latmcl
    syl3anc
    adantr
    cB
    c.or
    cK
    cC
    @16
    cdlemefr29.b
    cdlemefr29.j
    latjcl
    syl3anc
    expr
    adantrd
    ancld
    ex
    reximdai
    mpd
end
