include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crio.mm"
include "eqidd.mm"
include "wreu.mm"
include "wb.mm"
include "simp3.mm"
include "ltrnel.mm"
include "3com23.mm"
include "cdleme.mm"
include "syld3an3.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem cdlemeiota
  let cA: class A
  let cP: class P
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let cQ: class Q
  assume cdlemg1c.l: |- .<_ = ( le ` K )
  assume cdlemg1c.a: |- A = ( Atoms ` K )
  assume cdlemg1c.h: |- H = ( LHyp ` K )
  assume cdlemg1c.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A f
  disjoint F f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint T f
  disjoint W f
  disjoint f p
  disjoint f q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint F p
  disjoint F q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint Q f
  disjoint T p
  disjoint T q
  disjoint W p
  disjoint W q
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ F e. T ) -> F = ( iota_ f e. T ( f ` P ) = ( F ` P ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cF
    cT
    wcel
    #
    w3a
    #
    cP
    vf
    cv
    #
    cfv
    #
    cP
    cF
    cfv
    #
    wceq
    #
    vf
    cT
    crio
    #
    cF
    @3
    @6
    @6
    wceq
    #
    @8
    cF
    wceq
    #
    @3
    @6
    eqidd
    @3
    @2
    @7
    vf
    cT
    wreu
    #
    @9
    @10
    wb
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    @6
    cA
    wcel
    @6
    cW
    c.le
    wbr
    wn
    wa
    #
    @11
    @0
    @2
    @1
    @12
    cA
    cP
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
    3com23
    cA
    cP
    @6
    cT
    vf
    cH
    cK
    c.le
    cW
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    cdlemg1c.t
    cdleme
    syld3an3
    @7
    @9
    vf
    cT
    cF
    @4
    cF
    wceq
    @5
    @6
    @6
    cP
    @4
    cF
    fveq1
    eqeq1d
    riota2
    syl2anc
    mpbid
    eqcomd
end
