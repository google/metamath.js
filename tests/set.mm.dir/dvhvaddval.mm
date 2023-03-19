include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "coeq1d.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "coeq2d.mm"
include "oveq2d.mm"
include "dvhvaddcbv.mm"
include "opex.mm"
include "ovmpt2.mm"

theorem dvhvaddval
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let vh: setvar h
  let vi: setvar i
  assume dvhvaddval.a: |- .+ = ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( ( 2nd ` f ) .+^ ( 2nd ` g ) ) >. )

  disjoint f g
  disjoint E f
  disjoint E g
  disjoint .+^ f
  disjoint .+^ g
  disjoint T f
  disjoint T g
  disjoint f h
  disjoint f i
  disjoint g h
  disjoint g i
  disjoint h i
  disjoint E h
  disjoint E i
  disjoint .+^ h
  disjoint .+^ i
  disjoint T h
  disjoint T i
  disjoint F h
  disjoint F i
  disjoint G h
  disjoint G i
  assert |- ( ( F e. ( T X. E ) /\ G e. ( T X. E ) ) -> ( F .+ G ) = <. ( ( 1st ` F ) o. ( 1st ` G ) ) , ( ( 2nd ` F ) .+^ ( 2nd ` G ) ) >. )

  proof
    vh
    vi
    cF
    cG
    cT
    cE
    cxp
    #
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
    cF
    c1st
    cfv
    #
    cG
    c1st
    cfv
    #
    ccom
    #
    cF
    c2nd
    cfv
    #
    cG
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    c.pl
    @9
    @4
    ccom
    #
    @12
    @7
    c.pd
    co
    #
    cop
    @1
    cF
    wceq
    #
    @5
    @15
    @8
    @16
    @17
    @2
    @9
    @4
    @1
    cF
    c1st
    fveq2
    coeq1d
    @17
    @6
    @12
    @7
    c.pd
    @1
    cF
    c2nd
    fveq2
    oveq1d
    opeq12d
    @3
    cG
    wceq
    #
    @15
    @11
    @16
    @14
    @18
    @4
    @10
    @9
    @3
    cG
    c1st
    fveq2
    coeq2d
    @18
    @7
    @13
    @12
    c.pd
    @3
    cG
    c2nd
    fveq2
    oveq2d
    opeq12d
    c.pl
    c.pd
    cT
    vf
    vg
    vh
    vi
    cE
    dvhvaddval.a
    dvhvaddcbv
    @11
    @14
    opex
    ovmpt2
end
