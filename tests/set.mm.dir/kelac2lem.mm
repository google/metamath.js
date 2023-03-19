include "wcel.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cpr.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "cfn.mm"
include "cin.mm"
include "ccmp.mm"
include "ctb.mm"
include "cvv.mm"
include "weq.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "prex.mm"
include "vex.mm"
include "elpr.mm"
include "wa.mm"
include "eqtr3.mm"
include "orcd.mm"
include "ineq12.mm"
include "incom.mm"
include "wn.mm"
include "pwuninel.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "olcd.mm"
include "ccase.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "baspartn.mm"
include "mp2an.mm"
include "tgcl.mm"
include "mp1i.mm"
include "cdom.mm"
include "wbr.mm"
include "prfi.mm"
include "pwfi.mm"
include "mpbi.mm"
include "tgdom.mm"
include "ax-mp.mm"
include "domfi.mm"
include "a1i.mm"
include "elind.mm"
include "fincmp.mm"
include "syl.mm"

theorem kelac2lem
  let cS: class S
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( S e. V -> ( topGen ` { S , { ~P U. S } } ) e. Comp )

  proof
    cS
    cV
    wcel
    #
    cS
    cS
    cuni
    cpw
    #
    csn
    #
    cpr
    #
    ctg
    cfv
    #
    ctop
    cfn
    cin
    wcel
    @4
    ccmp
    wcel
    @0
    ctop
    cfn
    @4
    @3
    ctb
    wcel
    #
    @4
    ctop
    wcel
    @0
    @3
    cvv
    wcel
    #
    vx
    vy
    weq
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    @3
    wral
    vx
    @3
    wral
    @5
    cS
    @2
    prex
    #
    @12
    vx
    vy
    @3
    @8
    @3
    wcel
    @8
    cS
    wceq
    #
    @8
    @2
    wceq
    #
    wo
    @9
    cS
    wceq
    #
    @9
    @2
    wceq
    #
    wo
    @12
    @9
    @3
    wcel
    @8
    cS
    @2
    vx
    vex
    elpr
    @9
    cS
    @2
    vy
    vex
    elpr
    @14
    @16
    @15
    @17
    @12
    @14
    @16
    wa
    @7
    @11
    @8
    @9
    cS
    eqtr3
    orcd
    @15
    @16
    wa
    #
    @11
    @7
    @18
    @10
    @2
    cS
    cin
    #
    c0
    @8
    @2
    @9
    cS
    ineq12
    @19
    cS
    @2
    cin
    #
    c0
    @2
    cS
    incom
    @20
    c0
    wceq
    @1
    cS
    wcel
    wn
    cS
    pwuninel
    cS
    @1
    disjsn
    mpbir
    #
    eqtri
    syl6eq
    olcd
    @14
    @17
    wa
    #
    @11
    @7
    @22
    @10
    @20
    c0
    @8
    cS
    @9
    @2
    ineq12
    @21
    syl6eq
    olcd
    @15
    @17
    wa
    @7
    @11
    @8
    @9
    @2
    eqtr3
    orcd
    ccase
    syl2anb
    rgen2a
    vx
    vy
    @3
    cvv
    baspartn
    mp2an
    @3
    tgcl
    mp1i
    @4
    cfn
    wcel
    #
    @0
    @3
    cpw
    #
    cfn
    wcel
    #
    @4
    @24
    cdom
    wbr
    #
    @23
    @3
    cfn
    wcel
    @25
    cS
    @2
    prfi
    @3
    pwfi
    mpbi
    @6
    @26
    @13
    @3
    cvv
    tgdom
    ax-mp
    @24
    @4
    domfi
    mp2an
    a1i
    elind
    @4
    fincmp
    syl
end
