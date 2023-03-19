include "cv.mm"
include "cjn.mm"
include "cfv.mm"
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
include "cdlemg1idlemN.mm"

theorem cdlemg1idN
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdlemg1ltrn.l: |- .<_ = ( le ` K )
  assume cdlemg1ltrn.a: |- A = ( Atoms ` K )
  assume cdlemg1ltrn.h: |- H = ( LHyp ` K )
  assume cdlemg1ltrn.f: |- F = ( iota_ f e. T ( f ` P ) = Q )
  assume cdlemg1ltrn.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg1id.b: |- B = ( Base ` K )

  disjoint A f
  disjoint B f
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
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
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
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ X e. B ) /\ P = Q ) -> ( F ` X ) = X )

  proof
    vx
    vy
    vz
    vt
    cA
    cB
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
    @1
    co
    cQ
    cP
    @0
    @1
    co
    cW
    @3
    co
    @1
    co
    @3
    co
    #
    cP
    cQ
    cT
    @4
    vf
    @2
    @5
    vs
    cv
    #
    @0
    @1
    co
    cW
    @3
    co
    @1
    co
    @3
    co
    #
    cF
    vx
    cB
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
    @6
    cW
    c.le
    wbr
    wn
    @6
    @8
    cW
    @3
    co
    #
    @1
    co
    @8
    wceq
    wa
    vz
    cv
    @6
    @2
    c.le
    wbr
    @0
    cW
    c.le
    wbr
    wn
    @0
    @2
    c.le
    wbr
    wn
    wa
    vy
    cv
    @7
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    vt
    @6
    @5
    csb
    cif
    @9
    @1
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    @8
    cif
    cmpt
    #
    cH
    @1
    cK
    c.le
    @3
    cW
    cX
    vs
    cdlemg1id.b
    cdlemg1ltrn.l
    @1
    eqid
    @3
    eqid
    cdlemg1ltrn.a
    cdlemg1ltrn.h
    @4
    eqid
    @5
    eqid
    @7
    eqid
    @10
    eqid
    cdlemg1ltrn.t
    cdlemg1ltrn.f
    cdlemg1idlemN
end
