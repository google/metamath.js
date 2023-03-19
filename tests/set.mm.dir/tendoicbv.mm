include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "cmpt.mm"
include "weq.mm"
include "fveq1.mm"
include "cnveqd.mm"
include "mpteq2dv.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "eqtri.mm"

theorem tendoicbv
  let vu: setvar u
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cI: class I
  let vs: setvar s
  let cW: class W
  assume tendoi.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )

  disjoint s u
  disjoint E s
  disjoint E u
  disjoint f g
  disjoint f s
  disjoint f u
  disjoint T f
  disjoint g s
  disjoint g u
  disjoint T g
  disjoint T s
  disjoint T u
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W u
  assert |- I = ( u e. E |-> ( g e. T |-> `' ( u ` g ) ) )

  proof
    cI
    vs
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
    ccnv
    #
    cmpt
    #
    cmpt
    vu
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
    ccnv
    #
    cmpt
    #
    cmpt
    tendoi.i
    vs
    vu
    cE
    @4
    @9
    vs
    vu
    weq
    #
    @4
    vf
    cT
    @0
    @6
    cfv
    #
    ccnv
    #
    cmpt
    @9
    @10
    vf
    cT
    @3
    @12
    @10
    @2
    @11
    @0
    @1
    @6
    fveq1
    cnveqd
    mpteq2dv
    vf
    vg
    cT
    @12
    @8
    vf
    vg
    weq
    @11
    @7
    @0
    @5
    @6
    fveq2
    cnveqd
    cbvmptv
    syl6eq
    cbvmptv
    eqtri
end
