include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "weq.mm"
include "fveq1.mm"
include "coeq1d.mm"
include "mpteq2dv.mm"
include "coeq2d.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"

theorem tendoplcbv
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let vs: setvar s
  let cW: class W
  assume tendoplcbv.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )

  disjoint s t
  disjoint s u
  disjoint s v
  disjoint E s
  disjoint t u
  disjoint t v
  disjoint E t
  disjoint u v
  disjoint E u
  disjoint E v
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint T f
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint T g
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W v
  assert |- P = ( u e. E , v e. E |-> ( g e. T |-> ( ( u ` g ) o. ( v ` g ) ) ) )

  proof
    cP
    vs
    vt
    cE
    cE
    vf
    cT
    vf
    cv
    #
    vs
    cv
    #
    cfv
    #
    @0
    vt
    cv
    #
    cfv
    #
    ccom
    #
    cmpt
    #
    cmpt2
    vu
    vv
    cE
    cE
    vg
    cT
    vg
    cv
    #
    vu
    cv
    #
    cfv
    #
    @7
    vv
    cv
    #
    cfv
    #
    ccom
    #
    cmpt
    #
    cmpt2
    tendoplcbv.p
    vs
    vt
    vu
    vv
    cE
    cE
    @6
    @13
    vf
    cT
    @0
    @8
    cfv
    #
    @4
    ccom
    #
    cmpt
    #
    vs
    vu
    weq
    #
    vf
    cT
    @5
    @15
    @17
    @2
    @14
    @4
    @0
    @1
    @8
    fveq1
    coeq1d
    mpteq2dv
    vt
    vv
    weq
    #
    @16
    vf
    cT
    @14
    @0
    @10
    cfv
    #
    ccom
    #
    cmpt
    @13
    @18
    vf
    cT
    @15
    @20
    @18
    @4
    @19
    @14
    @0
    @3
    @10
    fveq1
    coeq2d
    mpteq2dv
    vf
    vg
    cT
    @20
    @12
    vf
    vg
    weq
    @14
    @9
    @19
    @11
    @0
    @7
    @8
    fveq2
    @0
    @7
    @10
    fveq2
    coeq12d
    cbvmptv
    syl6eq
    cbvmpt2v
    eqtri
end
