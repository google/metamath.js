include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "crio.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpr.mm"
include "cdlemeiota.mm"
include "syl3anc.mm"
include "simplr.mm"
include "eqeq2d.mm"
include "riotabidv.mm"
include "eqtrd.mm"
include "cdlemg1ci2.mm"
include "adantlr.mm"
include "impbida.mm"

theorem cdlemg1cN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vq: setvar q
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
  disjoint Q f
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
  disjoint T p
  disjoint T q
  disjoint W p
  disjoint W q
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F ` P ) = Q ) -> ( F e. T <-> F = ( iota_ f e. T ( f ` P ) = Q ) ) )

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
    cF
    cfv
    #
    cQ
    wceq
    #
    wa
    #
    cF
    cT
    wcel
    #
    cF
    cP
    vf
    cv
    cfv
    #
    cQ
    wceq
    #
    vf
    cT
    crio
    #
    wceq
    #
    @6
    @7
    wa
    #
    cF
    @8
    @4
    wceq
    #
    vf
    cT
    crio
    #
    @10
    @12
    @0
    @1
    @7
    cF
    @14
    wceq
    @0
    @1
    @2
    @5
    @7
    simpll1
    @0
    @1
    @2
    @5
    @7
    simpll2
    @6
    @7
    simpr
    cA
    cP
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
    @12
    @13
    @9
    vf
    cT
    @12
    @4
    cQ
    @8
    @3
    @5
    @7
    simplr
    eqeq2d
    riotabidv
    eqtrd
    @3
    @11
    @7
    @5
    cA
    cP
    cQ
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
    adantlr
    impbida
end
