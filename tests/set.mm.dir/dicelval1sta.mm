include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "w3a.mm"
include "c1st.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "c2nd.mm"
include "ctendo.mm"
include "copab.mm"
include "eqid.mm"
include "dicval.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "elopabi.mm"
include "syl.mm"
include "simpld.mm"

theorem dicelval1sta
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vs: setvar s
  assume dicelval1sta.l: |- .<_ = ( le ` K )
  assume dicelval1sta.a: |- A = ( Atoms ` K )
  assume dicelval1sta.h: |- H = ( LHyp ` K )
  assume dicelval1sta.p: |- P = ( ( oc ` K ) ` W )
  assume dicelval1sta.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicelval1sta.i: |- I = ( ( DIsoC ` K ) ` W )

  disjoint K g
  disjoint Q g
  disjoint T g
  disjoint W g
  disjoint f g
  disjoint f s
  disjoint K f
  disjoint g s
  disjoint K s
  disjoint P f
  disjoint P s
  disjoint Q f
  disjoint Q s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint Y f
  disjoint Y s
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ Y e. ( I ` Q ) ) -> ( 1st ` Y ) = ( ( 2nd ` Y ) ` ( iota_ g e. T ( g ` P ) = Q ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
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
    cY
    cQ
    cI
    cfv
    #
    wcel
    #
    w3a
    #
    cY
    c1st
    cfv
    #
    cP
    vg
    cv
    cfv
    cQ
    wceq
    vg
    cT
    crio
    #
    cY
    c2nd
    cfv
    #
    cfv
    #
    wceq
    #
    @7
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @4
    cY
    vf
    cv
    #
    @6
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @13
    @10
    wcel
    #
    wa
    #
    vf
    vs
    copab
    #
    wcel
    #
    @9
    @11
    wa
    #
    @0
    @1
    @3
    @19
    @0
    @1
    wa
    @2
    @18
    cY
    cA
    cP
    cQ
    cT
    vf
    vg
    @10
    cH
    cI
    cK
    c.le
    cV
    cW
    vs
    dicelval1sta.l
    dicelval1sta.a
    dicelval1sta.h
    dicelval1sta.p
    dicelval1sta.t
    @10
    eqid
    dicelval1sta.i
    dicval
    eleq2d
    biimp3a
    @17
    @5
    @14
    wceq
    #
    @16
    wa
    @20
    vf
    vs
    cY
    @12
    @5
    wceq
    @15
    @21
    @16
    @12
    @5
    @14
    eqeq1
    anbi1d
    @13
    @7
    wceq
    #
    @21
    @9
    @16
    @11
    @22
    @14
    @8
    @5
    @6
    @13
    @7
    fveq1
    eqeq2d
    @13
    @7
    @10
    eleq1
    anbi12d
    elopabi
    syl
    simpld
end
