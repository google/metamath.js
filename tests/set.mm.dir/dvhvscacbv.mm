include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cop.mm"
include "cmpt2.mm"
include "weq.mm"
include "fveq1.mm"
include "coeq1.mm"
include "opeq12d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "coeq2d.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"

theorem dvhvscacbv
  let vt: setvar t
  let cT: class T
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let vs: setvar s
  assume dvhvscaval.s: |- .x. = ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. )

  disjoint f s
  disjoint s t
  disjoint g s
  disjoint E s
  disjoint f t
  disjoint f g
  disjoint E f
  disjoint g t
  disjoint E t
  disjoint E g
  disjoint T s
  disjoint T f
  disjoint T t
  disjoint T g
  assert |- .x. = ( t e. E , g e. ( T X. E ) |-> <. ( t ` ( 1st ` g ) ) , ( t o. ( 2nd ` g ) ) >. )

  proof
    c.x
    vs
    vf
    cE
    cT
    cE
    cxp
    #
    vf
    cv
    #
    c1st
    cfv
    #
    vs
    cv
    #
    cfv
    #
    @3
    @1
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    cmpt2
    vt
    vg
    cE
    @0
    vg
    cv
    #
    c1st
    cfv
    #
    vt
    cv
    #
    cfv
    #
    @10
    @8
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    cmpt2
    dvhvscaval.s
    vs
    vf
    vt
    vg
    cE
    @0
    @7
    @14
    @2
    @10
    cfv
    #
    @10
    @5
    ccom
    #
    cop
    vs
    vt
    weq
    @4
    @15
    @6
    @16
    @2
    @3
    @10
    fveq1
    @3
    @10
    @5
    coeq1
    opeq12d
    vf
    vg
    weq
    #
    @15
    @11
    @16
    @13
    @17
    @2
    @9
    @10
    @1
    @8
    c1st
    fveq2
    fveq2d
    @17
    @5
    @12
    @10
    @1
    @8
    c2nd
    fveq2
    coeq2d
    opeq12d
    cbvmpt2v
    eqtri
end
