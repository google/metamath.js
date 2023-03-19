include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "crio.mm"
include "w3a.mm"
include "wrex.mm"
include "ltrnel.mm"
include "3expa.mm"
include "simpld.mm"
include "simprr.mm"
include "simprd.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "cdlemeiota.mm"
include "syl3anc.mm"
include "breq1.mm"
include "notbid.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "lhpexnle.mm"
include "adantr.mm"
include "reximddv.mm"
include "ex.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp31.mm"
include "jca.mm"
include "simp2r.mm"
include "simp32.mm"
include "simp33.mm"
include "cdlemg1ci2.mm"
include "syl31anc.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impbid.mm"

theorem cdlemg1cex
  let cA: class A
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  let cP: class P
  let cQ: class Q
  assume cdlemg1c.l: |- .<_ = ( le ` K )
  assume cdlemg1c.a: |- A = ( Atoms ` K )
  assume cdlemg1c.h: |- H = ( LHyp ` K )
  assume cdlemg1c.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint f p
  disjoint f q
  disjoint A f
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint F f
  disjoint F p
  disjoint F q
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint K f
  disjoint K p
  disjoint K q
  disjoint .<_ f
  disjoint .<_ p
  disjoint .<_ q
  disjoint T f
  disjoint T p
  disjoint T q
  disjoint W f
  disjoint W p
  disjoint W q
  disjoint P f
  disjoint Q f
  assert |- ( ( K e. HL /\ W e. H ) -> ( F e. T <-> E. p e. A E. q e. A ( -. p .<_ W /\ -. q .<_ W /\ F = ( iota_ f e. T ( f ` p ) = q ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cF
    @2
    vf
    cv
    cfv
    #
    @4
    wceq
    #
    vf
    cT
    crio
    #
    wceq
    #
    w3a
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    @0
    @1
    @13
    @0
    @1
    wa
    #
    @3
    @12
    vp
    cA
    @14
    @2
    cA
    wcel
    #
    @3
    wa
    #
    wa
    #
    @2
    cF
    cfv
    #
    cA
    wcel
    #
    @3
    @18
    cW
    c.le
    wbr
    #
    wn
    #
    cF
    @7
    @18
    wceq
    #
    vf
    cT
    crio
    #
    wceq
    #
    @12
    @17
    @19
    @21
    @0
    @1
    @16
    @19
    @21
    wa
    cA
    @2
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    cdlemg1c.t
    ltrnel
    3expa
    #
    simpld
    @14
    @15
    @3
    simprr
    @17
    @19
    @21
    @25
    simprd
    @17
    @0
    @16
    @1
    @24
    @0
    @1
    @16
    simpll
    @14
    @16
    simpr
    @0
    @1
    @16
    simplr
    cA
    @2
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    cdlemg1c.t
    cdlemeiota
    syl3anc
    @11
    @3
    @21
    @24
    w3a
    vq
    @18
    cA
    @4
    @18
    wceq
    #
    @6
    @21
    @10
    @24
    @3
    @26
    @5
    @20
    @4
    @18
    cW
    c.le
    breq1
    notbid
    @26
    @9
    @23
    cF
    @26
    @8
    @22
    vf
    cT
    @4
    @18
    @7
    eqeq2
    riotabidv
    eqeq2d
    3anbi23d
    rspcev
    syl13anc
    @0
    @3
    vp
    cA
    wrex
    @1
    cA
    cH
    cK
    c.le
    cW
    vp
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    lhpexnle
    adantr
    reximddv
    ex
    @0
    @11
    @1
    vp
    vq
    cA
    cA
    @0
    @15
    @4
    cA
    wcel
    #
    wa
    #
    @11
    @1
    @0
    @28
    @11
    w3a
    #
    @0
    @16
    @27
    @6
    wa
    @10
    @1
    @0
    @28
    @11
    simp1
    @29
    @15
    @3
    @0
    @15
    @27
    @11
    simp2l
    @0
    @28
    @3
    @6
    @10
    simp31
    jca
    @29
    @27
    @6
    @0
    @15
    @27
    @11
    simp2r
    @0
    @28
    @3
    @6
    @10
    simp32
    jca
    @0
    @28
    @3
    @6
    @10
    simp33
    cA
    @2
    @4
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    cdlemg1c.t
    cdlemg1ci2
    syl31anc
    3exp
    rexlimdvv
    impbid
end
