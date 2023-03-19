include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cop.mm"
include "wceq.mm"
include "fveq1.mm"
include "coeq1.mm"
include "opeq12d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "coeq2d.mm"
include "dvhvscacbv.mm"
include "opex.mm"
include "ovmpt2.mm"

theorem dvhvscaval
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vg: setvar g
  assume dvhvscaval.s: |- .x. = ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. )

  disjoint f s
  disjoint E s
  disjoint E f
  disjoint T s
  disjoint T f
  disjoint s t
  disjoint g s
  disjoint f t
  disjoint f g
  disjoint g t
  disjoint E t
  disjoint E g
  disjoint T t
  disjoint T g
  disjoint U t
  disjoint U g
  disjoint F t
  disjoint F g
  assert |- ( ( U e. E /\ F e. ( T X. E ) ) -> ( U .x. F ) = <. ( U ` ( 1st ` F ) ) , ( U o. ( 2nd ` F ) ) >. )

  proof
    vt
    vg
    cU
    cF
    cE
    cT
    cE
    cxp
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
    @2
    @0
    c2nd
    cfv
    #
    ccom
    #
    cop
    cF
    c1st
    cfv
    #
    cU
    cfv
    #
    cU
    cF
    c2nd
    cfv
    #
    ccom
    #
    cop
    c.x
    @1
    cU
    cfv
    #
    cU
    @4
    ccom
    #
    cop
    @2
    cU
    wceq
    @3
    @10
    @5
    @11
    @1
    @2
    cU
    fveq1
    @2
    cU
    @4
    coeq1
    opeq12d
    @0
    cF
    wceq
    #
    @10
    @7
    @11
    @9
    @12
    @1
    @6
    cU
    @0
    cF
    c1st
    fveq2
    fveq2d
    @12
    @4
    @8
    cU
    @0
    cF
    c2nd
    fveq2
    coeq2d
    opeq12d
    vt
    cT
    c.x
    vf
    vg
    cE
    vs
    dvhvscaval.s
    dvhvscacbv
    @7
    @9
    opex
    ovmpt2
end
