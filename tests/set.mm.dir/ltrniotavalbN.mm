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
include "simpl1.mm"
include "simpl3.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "eqid.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ltrniotaval.mm"
include "eqtr4d.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "fveq1.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "sylan9eqr.mm"
include "impbida.mm"

theorem ltrniotavalbN
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
  assume ltrniotavalb.l: |- .<_ = ( le ` K )
  assume ltrniotavalb.a: |- A = ( Atoms ` K )
  assume ltrniotavalb.h: |- H = ( LHyp ` K )
  assume ltrniotavalb.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint .<_ f
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( ( F ` P ) = Q <-> F = ( iota_ f e. T ( f ` P ) = Q ) ) )

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
    wa
    #
    cF
    cT
    wcel
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
    @5
    @7
    wa
    #
    @0
    @4
    @8
    cT
    wcel
    #
    @1
    @6
    cP
    @8
    cfv
    #
    wceq
    @9
    @0
    @3
    @4
    @7
    simpl1
    #
    @0
    @3
    @4
    @7
    simpl3
    @10
    @0
    @1
    @2
    @11
    @13
    @1
    @2
    @0
    @4
    @7
    simpl2l
    #
    @1
    @2
    @0
    @4
    @7
    simpl2r
    #
    cA
    cP
    cQ
    cT
    vf
    @8
    cH
    cK
    c.le
    cW
    ltrniotavalb.l
    ltrniotavalb.a
    ltrniotavalb.h
    ltrniotavalb.t
    @8
    eqid
    #
    ltrniotacl
    syl3anc
    @14
    @10
    @6
    cQ
    @12
    @5
    @7
    simpr
    @10
    @0
    @1
    @2
    @12
    cQ
    wceq
    #
    @13
    @14
    @15
    cA
    cP
    cQ
    cT
    vf
    @8
    cH
    cK
    c.le
    cW
    ltrniotavalb.l
    ltrniotavalb.a
    ltrniotavalb.h
    ltrniotavalb.t
    @16
    ltrniotaval
    #
    syl3anc
    eqtr4d
    cA
    cP
    cT
    cF
    @8
    cH
    cK
    c.le
    cW
    ltrniotavalb.l
    ltrniotavalb.a
    ltrniotavalb.h
    ltrniotavalb.t
    cdlemd
    syl311anc
    @9
    @5
    @6
    @12
    cQ
    cP
    cF
    @8
    fveq1
    @5
    @0
    @1
    @2
    @17
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2l
    @0
    @1
    @2
    @4
    simp2r
    @18
    syl3anc
    sylan9eqr
    impbida
end
