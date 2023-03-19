include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "wceq.mm"
include "ccnv.mm"
include "simp1.mm"
include "ltrniotacl.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "simp2l.mm"
include "atbase.mm"
include "syl.mm"
include "jca.mm"
include "ltrniotaval.mm"
include "f1ocnvfv.mm"
include "sylc.mm"

theorem ltrniotacnvval
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( `' F ` Q ) = P )

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
    #
    cP
    cW
    c.le
    wbr
    wn
    #
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
    cK
    cbs
    cfv
    #
    @6
    cF
    wf1o
    #
    cP
    @6
    wcel
    #
    wa
    cP
    cF
    cfv
    cQ
    wceq
    cQ
    cF
    ccnv
    cfv
    cP
    wceq
    @5
    @7
    @8
    @5
    @0
    cF
    cT
    wcel
    @7
    @0
    @3
    @4
    simp1
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
    ltrniotaval.l
    ltrniotaval.a
    ltrniotaval.h
    ltrniotaval.t
    ltrniotaval.f
    ltrniotacl
    @6
    cT
    cF
    cH
    cK
    chlt
    cW
    @6
    eqid
    #
    ltrniotaval.h
    ltrniotaval.t
    ltrn1o
    syl2anc
    @5
    @1
    @8
    @0
    @1
    @2
    @4
    simp2l
    cA
    @6
    cP
    cK
    @9
    ltrniotaval.a
    atbase
    syl
    jca
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
    ltrniotaval.l
    ltrniotaval.a
    ltrniotaval.h
    ltrniotaval.t
    ltrniotaval.f
    ltrniotaval
    @6
    @6
    cP
    cQ
    cF
    f1ocnvfv
    sylc
end
