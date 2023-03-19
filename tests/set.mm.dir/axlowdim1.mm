include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cee.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "cr.mm"
include "wf.mm"
include "1re.mm"
include "fconst6.mm"
include "elee.mm"
include "mpbiri.mm"
include "0re.mm"
include "crn.mm"
include "wceq.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "1ex.mm"
include "sneqr.mm"
include "mto.mm"
include "c0.mm"
include "cuz.mm"
include "elnnuz.mm"
include "eluzfz1.mm"
include "sylbi.mm"
include "ne0i.mm"
include "syl.mm"
include "rnxp.mm"
include "eqeq12d.mm"
include "mtbiri.mm"
include "rneq.mm"
include "nsyl.mm"
include "neqned.mm"
include "neeq1.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"

theorem axlowdim1
  let vx: setvar x
  let vy: setvar y
  let cN: class N

  disjoint N x
  disjoint N y
  disjoint x y
  assert |- ( N e. NN -> E. x e. ( EE ` N ) E. y e. ( EE ` N ) x =/= y )

  proof
    cN
    cn
    wcel
    #
    c1
    cN
    cfz
    co
    #
    c1
    csn
    #
    cxp
    #
    cN
    cee
    cfv
    #
    wcel
    #
    @1
    cc0
    csn
    #
    cxp
    #
    @4
    wcel
    #
    @3
    @7
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    @4
    wrex
    vx
    @4
    wrex
    @0
    @5
    @1
    cr
    @3
    wf
    @1
    c1
    cr
    1re
    fconst6
    @3
    cN
    elee
    mpbiri
    @0
    @8
    @1
    cr
    @7
    wf
    @1
    cc0
    cr
    0re
    fconst6
    @7
    cN
    elee
    mpbiri
    @0
    @3
    @7
    @0
    @3
    crn
    #
    @7
    crn
    #
    wceq
    #
    @3
    @7
    wceq
    @0
    @15
    @2
    @6
    wceq
    #
    @16
    c1
    cc0
    wceq
    c1
    cc0
    ax-1ne0
    neii
    c1
    cc0
    1ex
    sneqr
    mto
    @0
    @13
    @2
    @14
    @6
    @0
    @1
    c0
    wne
    #
    @13
    @2
    wceq
    @0
    c1
    @1
    wcel
    #
    @17
    @0
    cN
    c1
    cuz
    cfv
    wcel
    @18
    cN
    elnnuz
    c1
    cN
    eluzfz1
    sylbi
    @1
    c1
    ne0i
    syl
    #
    @1
    @2
    rnxp
    syl
    @0
    @17
    @14
    @6
    wceq
    @19
    @1
    @6
    rnxp
    syl
    eqeq12d
    mtbiri
    @3
    @7
    rneq
    nsyl
    neqned
    @12
    @9
    @3
    @11
    wne
    vx
    vy
    @3
    @7
    @4
    @4
    @10
    @3
    @11
    neeq1
    @11
    @7
    @3
    neeq2
    rspc2ev
    syl3anc
end
