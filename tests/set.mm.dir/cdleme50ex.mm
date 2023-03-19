include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cmpt.mm"
include "wrex.mm"
include "eqid.mm"
include "cdleme50ltrn.mm"
include "cdleme17d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem cdleme50ex
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> E. f e. T ( f ` P ) = Q )

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
    vx
    cK
    cbs
    cfv
    #
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
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @2
    @1
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    @1
    wceq
    wa
    vz
    cv
    @2
    cP
    cQ
    @5
    co
    #
    c.le
    wbr
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @7
    @6
    c.le
    wbr
    wn
    wa
    vy
    cv
    @6
    @7
    @6
    cW
    @3
    co
    #
    @5
    co
    cQ
    cP
    @7
    @5
    co
    cW
    @3
    co
    @5
    co
    @3
    co
    #
    @2
    @7
    @5
    co
    cW
    @3
    co
    @5
    co
    @3
    co
    #
    wceq
    wi
    vt
    cA
    wral
    vy
    @0
    crio
    vt
    @2
    @9
    csb
    cif
    @4
    @5
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    @0
    crio
    @1
    cif
    cmpt
    #
    cT
    wcel
    cP
    @11
    cfv
    #
    cQ
    wceq
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
    vx
    vy
    vz
    vt
    cA
    @0
    @9
    cP
    cQ
    cT
    @8
    @10
    @11
    cH
    @5
    cK
    c.le
    @3
    cW
    vs
    @0
    eqid
    #
    cdleme.l
    @5
    eqid
    #
    @3
    eqid
    #
    cdleme.a
    cdleme.h
    @8
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    cdleme.t
    cdleme50ltrn
    vx
    vy
    vz
    vt
    cA
    @0
    @9
    cP
    cQ
    @8
    @10
    @11
    cH
    @5
    cK
    c.le
    @3
    cW
    vs
    @17
    cdleme.l
    @18
    @19
    cdleme.a
    cdleme.h
    @20
    @21
    @22
    @23
    cdleme17d
    @16
    @13
    vf
    @11
    cT
    @14
    @11
    wceq
    @15
    @12
    cQ
    cP
    @14
    @11
    fveq1
    eqeq1d
    rspcev
    syl2anc
end
