include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemg1fvawlemN.mm"

theorem ltrniotafvawN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( ( F ` R ) e. A /\ -. ( F ` R ) .<_ W ) )

  proof
    vx
    vy
    vz
    vt
    cA
    cK
    cbs
    cfv
    #
    vt
    cv
    #
    cP
    cQ
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    @2
    co
    cQ
    cP
    @1
    @2
    co
    cW
    @4
    co
    @2
    co
    @4
    co
    #
    cP
    cQ
    cR
    cT
    @5
    vf
    @3
    @6
    vs
    cv
    #
    @1
    @2
    co
    cW
    @4
    co
    @2
    co
    @4
    co
    #
    cF
    vx
    @0
    cP
    cQ
    wne
    vx
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    @7
    cW
    c.le
    wbr
    wn
    @7
    @9
    cW
    @4
    co
    #
    @2
    co
    @9
    wceq
    wa
    vz
    cv
    @7
    @3
    c.le
    wbr
    @1
    cW
    c.le
    wbr
    wn
    @1
    @3
    c.le
    wbr
    wn
    wa
    vy
    cv
    @8
    wceq
    wi
    vt
    cA
    wral
    vy
    @0
    crio
    vt
    @7
    @6
    csb
    cif
    @10
    @2
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    @0
    crio
    @9
    cif
    cmpt
    #
    cH
    @2
    cK
    c.le
    @4
    cW
    vs
    @0
    eqid
    ltrniotaval.l
    @2
    eqid
    @4
    eqid
    ltrniotaval.a
    ltrniotaval.h
    @5
    eqid
    @6
    eqid
    @8
    eqid
    @11
    eqid
    ltrniotaval.t
    ltrniotaval.f
    cdlemg1fvawlemN
end
