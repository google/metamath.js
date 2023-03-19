include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wreu.mm"
include "cdleme.mm"
include "crio.mm"
include "nfriota1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "riotaprop.mm"
include "simprd.mm"
include "syl.mm"

theorem ltrniotaval
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
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  assume ltrniotaval.l: |- .<_ = ( le ` K )
  assume ltrniotaval.a: |- A = ( Atoms ` K )
  assume ltrniotaval.h: |- H = ( LHyp ` K )
  assume ltrniotaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume ltrniotaval.f: |- F = ( iota_ f e. T ( f ` P ) = Q )

  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
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
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( F ` P ) = Q )

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
    wreu
    #
    cP
    cF
    cfv
    #
    cQ
    wceq
    #
    cA
    cP
    cQ
    cT
    vf
    cH
    cK
    c.le
    cW
    ltrniotaval.l
    ltrniotaval.a
    ltrniotaval.h
    ltrniotaval.t
    cdleme
    @3
    cF
    cT
    wcel
    @5
    @2
    @5
    vf
    cT
    cF
    vf
    @4
    cQ
    vf
    cP
    cF
    vf
    cF
    @2
    vf
    cT
    crio
    ltrniotaval.f
    @2
    vf
    cT
    nfriota1
    nfcxfr
    vf
    cP
    nfcv
    nffv
    nfeq1
    ltrniotaval.f
    @0
    cF
    wceq
    @1
    @4
    cQ
    cP
    @0
    cF
    fveq1
    eqeq1d
    riotaprop
    simprd
    syl
end
