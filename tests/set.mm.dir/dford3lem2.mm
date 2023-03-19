include "cv.mm"
include "wtr.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wral.mm"
include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "suctr.mm"
include "vex.mm"
include "sucid.mm"
include "sucex.mm"
include "wceq.mm"
include "treq.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylancl.mm"
include "adantr.mm"
include "wi.mm"
include "word.mm"
include "wss.mm"
include "simprl.mm"
include "dford3lem1.mm"
include "ralim.mm"
include "syl5.mm"
include "imp.mm"
include "dfss3.mm"
include "sylibr.mm"
include "ordon.mm"
include "a1i.mm"
include "trssord.mm"
include "syl3anc.mm"
include "elon.mm"
include "ex.mm"
include "weq.mm"
include "raleq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "setindtrs.mm"
include "mpcom.mm"

theorem dford3lem2
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cN: class N

  disjoint x y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N x
  disjoint N y
  assert |- ( ( Tr x /\ A. y e. x Tr y ) -> x e. On )

  proof
    vc
    cv
    #
    wtr
    #
    vx
    vc
    wel
    #
    wa
    #
    vc
    wex
    #
    vx
    cv
    #
    wtr
    #
    vy
    cv
    wtr
    #
    vy
    @5
    wral
    #
    wa
    #
    @5
    con0
    wcel
    #
    @6
    @4
    @8
    @6
    @5
    csuc
    #
    wtr
    #
    @5
    @11
    wcel
    #
    @4
    @5
    suctr
    @5
    vx
    vex
    #
    sucid
    @3
    @12
    @13
    wa
    vc
    @11
    @5
    @14
    sucex
    @0
    @11
    wceq
    @1
    @12
    @2
    @13
    @0
    @11
    treq
    @0
    @11
    @5
    eleq2
    anbi12d
    spcev
    sylancl
    adantr
    va
    cv
    #
    wtr
    #
    @7
    vy
    @15
    wral
    #
    wa
    #
    @15
    con0
    wcel
    #
    wi
    vb
    cv
    #
    wtr
    #
    @7
    vy
    @20
    wral
    #
    wa
    #
    @20
    con0
    wcel
    #
    wi
    #
    @9
    @10
    wi
    va
    vb
    vc
    @5
    @25
    vb
    @15
    wral
    #
    @18
    @19
    @26
    @18
    wa
    #
    @15
    word
    #
    @19
    @27
    @16
    @15
    con0
    wss
    #
    con0
    word
    #
    @28
    @26
    @16
    @17
    simprl
    @27
    @24
    vb
    @15
    wral
    #
    @29
    @26
    @18
    @31
    @18
    @23
    vb
    @15
    wral
    @26
    @31
    vy
    @15
    vb
    dford3lem1
    @23
    @24
    vb
    @15
    ralim
    syl5
    imp
    vb
    @15
    con0
    dfss3
    sylibr
    @30
    @27
    ordon
    a1i
    @15
    con0
    trssord
    syl3anc
    @15
    va
    vex
    elon
    sylibr
    ex
    va
    vb
    weq
    #
    @18
    @23
    @19
    @24
    @32
    @16
    @21
    @17
    @22
    @15
    @20
    treq
    @7
    vy
    @15
    @20
    raleq
    anbi12d
    @15
    @20
    con0
    eleq1
    imbi12d
    va
    vx
    weq
    #
    @18
    @9
    @19
    @10
    @33
    @16
    @6
    @17
    @8
    @15
    @5
    treq
    @7
    vy
    @15
    @5
    raleq
    anbi12d
    @15
    @5
    con0
    eleq1
    imbi12d
    setindtrs
    mpcom
end
