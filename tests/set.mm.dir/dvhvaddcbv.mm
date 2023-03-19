include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "weq.mm"
include "fveq2.mm"
include "coeq1d.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "coeq2d.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"

theorem dvhvaddcbv
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let cE: class E
  assume dvhvaddval.a: |- .+ = ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( ( 2nd ` f ) .+^ ( 2nd ` g ) ) >. )

  disjoint f g
  disjoint f h
  disjoint f i
  disjoint E f
  disjoint g h
  disjoint g i
  disjoint E g
  disjoint h i
  disjoint E h
  disjoint E i
  disjoint .+^ f
  disjoint .+^ g
  disjoint .+^ h
  disjoint .+^ i
  disjoint T f
  disjoint T g
  disjoint T h
  disjoint T i
  assert |- .+ = ( h e. ( T X. E ) , i e. ( T X. E ) |-> <. ( ( 1st ` h ) o. ( 1st ` i ) ) , ( ( 2nd ` h ) .+^ ( 2nd ` i ) ) >. )

  proof
    c.pl
    vf
    vg
    cT
    cE
    cxp
    #
    @0
    vf
    cv
    #
    c1st
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    #
    ccom
    #
    @1
    c2nd
    cfv
    #
    @3
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    cmpt2
    vh
    vi
    @0
    @0
    vh
    cv
    #
    c1st
    cfv
    #
    vi
    cv
    #
    c1st
    cfv
    #
    ccom
    #
    @10
    c2nd
    cfv
    #
    @12
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    cmpt2
    dvhvaddval.a
    vf
    vg
    vh
    vi
    @0
    @0
    @9
    @18
    @11
    @4
    ccom
    #
    @15
    @7
    c.pd
    co
    #
    cop
    vf
    vh
    weq
    #
    @5
    @19
    @8
    @20
    @21
    @2
    @11
    @4
    @1
    @10
    c1st
    fveq2
    coeq1d
    @21
    @6
    @15
    @7
    c.pd
    @1
    @10
    c2nd
    fveq2
    oveq1d
    opeq12d
    vg
    vi
    weq
    #
    @19
    @14
    @20
    @17
    @22
    @4
    @13
    @11
    @3
    @12
    c1st
    fveq2
    coeq2d
    @22
    @7
    @16
    @15
    c.pd
    @3
    @12
    c2nd
    fveq2
    oveq2d
    opeq12d
    cbvmpt2v
    eqtri
end
