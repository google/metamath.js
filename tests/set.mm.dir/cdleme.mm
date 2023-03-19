include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cdleme50ex.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp12.mm"
include "eqtr3.mm"
include "3ad2ant3.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem cdleme
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdleme.l: |- .<_ = ( le ` K )
  assume cdleme.a: |- A = ( Atoms ` K )
  assume cdleme.h: |- H = ( LHyp ` K )
  assume cdleme.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  disjoint H f
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint T z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> E! f e. T ( f ` P ) = Q )

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
    vf
    cv
    #
    cfv
    #
    cQ
    wceq
    #
    vf
    cT
    wrex
    @6
    cP
    vz
    cv
    #
    cfv
    #
    cQ
    wceq
    #
    wa
    #
    @4
    @7
    wceq
    #
    wi
    #
    vz
    cT
    wral
    vf
    cT
    wral
    @6
    vf
    cT
    wreu
    cA
    cP
    cQ
    cT
    vf
    cH
    cK
    c.le
    cW
    cdleme.l
    cdleme.a
    cdleme.h
    cdleme.t
    cdleme50ex
    @3
    @12
    vf
    vz
    cT
    cT
    @3
    @4
    cT
    wcel
    #
    @7
    cT
    wcel
    #
    wa
    #
    @10
    @11
    @3
    @15
    @10
    w3a
    @0
    @13
    @14
    @1
    @5
    @8
    wceq
    #
    @11
    @0
    @1
    @2
    @15
    @10
    simp11
    @3
    @13
    @14
    @10
    simp2l
    @3
    @13
    @14
    @10
    simp2r
    @0
    @1
    @2
    @15
    @10
    simp12
    @10
    @3
    @16
    @15
    @5
    @8
    cQ
    eqtr3
    3ad2ant3
    cA
    cP
    cT
    @4
    @7
    cH
    cK
    c.le
    cW
    cdleme.l
    cdleme.a
    cdleme.h
    cdleme.t
    cdlemd
    syl311anc
    3exp
    ralrimivv
    @6
    @9
    vf
    vz
    cT
    @11
    @5
    @8
    cQ
    cP
    @4
    @7
    fveq1
    eqeq1d
    reu4
    sylanbrc
end
