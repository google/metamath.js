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
include "simpr.mm"
include "eqid.mm"
include "ltrniotacl.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem cdlemg1ci2
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F = ( iota_ f e. T ( f ` P ) = Q ) ) -> F e. T )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cF
    cP
    vf
    cv
    cfv
    cQ
    wceq
    vf
    cT
    crio
    #
    wceq
    #
    wa
    cF
    @1
    cT
    @0
    @2
    simpr
    @0
    @1
    cT
    wcel
    @2
    cA
    cP
    cQ
    cT
    vf
    @1
    cH
    cK
    c.le
    cW
    cdlemg1c.l
    cdlemg1c.a
    cdlemg1c.h
    cdlemg1c.t
    @1
    eqid
    ltrniotacl
    adantr
    eqeltrd
end
