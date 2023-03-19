include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cxp.mm"
include "wss.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wa.mm"
include "cv.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "ssun1.mm"
include "coundir.mm"
include "coundi.mm"
include "cossxp.mm"
include "ssun2.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"
include "dmxpss.mm"
include "unssi.mm"
include "eqsstri.mm"
include "rnxpss.mm"
include "xpidtr.mm"
include "dmun.mm"
include "rnun.mm"
include "ssres2.mm"
include "ax-mp.mm"
include "wrel.mm"
include "relres.mm"
include "relssdmrn.mm"
include "dmresi.mm"
include "rnresi.mm"
include "xpeq12i.mm"
include "sseqtri.mm"
include "id.mm"
include "wex.mm"
include "elexi.mm"
include "dmex.mm"
include "rnex.mm"
include "unex.mm"
include "xpex.mm"
include "wceq.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "anbi12d.mm"
include "cleq2lem.mm"
include "spcev.mm"
include "intexab.mm"
include "sylib.mm"

theorem rtrclexi
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rtrclexi.1: |- A e. V

  disjoint A x
  assert |- |^| { x | ( A C_ x /\ ( ( x o. x ) C_ x /\ ( _I |` ( dom x u. ran x ) ) C_ x ) ) } e. _V

  proof
    cA
    cA
    cA
    cdm
    #
    cA
    crn
    #
    cun
    #
    @2
    cxp
    #
    cun
    #
    wss
    #
    @4
    @4
    ccom
    #
    @4
    wss
    #
    cid
    @4
    cdm
    #
    @4
    crn
    #
    cun
    #
    cres
    #
    @4
    wss
    #
    wa
    #
    cA
    vx
    cv
    #
    wss
    @14
    @14
    ccom
    #
    @14
    wss
    #
    cid
    @14
    cdm
    #
    @14
    crn
    #
    cun
    #
    cres
    #
    @14
    wss
    #
    wa
    #
    wa
    #
    vx
    cab
    cint
    cvv
    wcel
    #
    cA
    @3
    ssun1
    @7
    @12
    @13
    @6
    @3
    @4
    @6
    cA
    @4
    ccom
    #
    @3
    @4
    ccom
    #
    cun
    @3
    cA
    @3
    @4
    coundir
    @25
    @26
    @3
    @25
    cA
    cA
    ccom
    #
    cA
    @3
    ccom
    #
    cun
    @3
    cA
    cA
    @3
    coundi
    @27
    @28
    @3
    @27
    @0
    @1
    cxp
    #
    @3
    cA
    cA
    cossxp
    @0
    @2
    wss
    #
    @1
    @2
    wss
    #
    @29
    @3
    wss
    @0
    @1
    ssun1
    #
    @1
    @0
    ssun2
    #
    @0
    @2
    @1
    @2
    xpss12
    mp2an
    sstri
    @28
    @3
    cdm
    #
    @1
    cxp
    #
    @3
    cA
    @3
    cossxp
    @34
    @2
    wss
    @31
    @35
    @3
    wss
    @2
    @2
    dmxpss
    #
    @33
    @34
    @2
    @1
    @2
    xpss12
    mp2an
    sstri
    unssi
    eqsstri
    @26
    @3
    cA
    ccom
    #
    @3
    @3
    ccom
    #
    cun
    @3
    @3
    cA
    @3
    coundi
    @37
    @38
    @3
    @37
    @0
    @3
    crn
    #
    cxp
    #
    @3
    @3
    cA
    cossxp
    @30
    @39
    @2
    wss
    @40
    @3
    wss
    @32
    @2
    @2
    rnxpss
    #
    @0
    @2
    @39
    @2
    xpss12
    mp2an
    sstri
    @2
    xpidtr
    unssi
    eqsstri
    unssi
    eqsstri
    @3
    cA
    ssun2
    #
    sstri
    @11
    @3
    @4
    @11
    cid
    @2
    cres
    #
    @3
    @10
    @2
    wss
    @11
    @43
    wss
    @8
    @9
    @2
    @8
    @0
    @34
    cun
    @2
    cA
    @3
    dmun
    @0
    @34
    @2
    @32
    @36
    unssi
    eqsstri
    @9
    @1
    @39
    cun
    @2
    cA
    @3
    rnun
    @1
    @39
    @2
    @33
    @41
    unssi
    eqsstri
    unssi
    @10
    @2
    cid
    ssres2
    ax-mp
    @43
    @43
    cdm
    #
    @43
    crn
    #
    cxp
    #
    @3
    @43
    wrel
    @43
    @46
    wss
    cid
    @2
    relres
    @43
    relssdmrn
    ax-mp
    @44
    @2
    @45
    @2
    @2
    dmresi
    @2
    rnresi
    xpeq12i
    sseqtri
    sstri
    @42
    sstri
    @13
    id
    mp2an
    @5
    @13
    wa
    #
    @23
    vx
    wex
    @24
    @23
    @47
    vx
    @4
    cA
    @3
    cA
    cV
    rtrclexi.1
    elexi
    #
    @2
    @2
    @0
    @1
    cA
    @48
    dmex
    cA
    @48
    rnex
    unex
    #
    @49
    xpex
    unex
    @22
    @13
    @14
    @4
    cA
    @14
    @4
    wceq
    #
    @16
    @7
    @21
    @12
    @50
    @15
    @6
    @14
    @4
    @50
    @14
    @4
    @14
    @4
    @50
    id
    #
    @51
    coeq12d
    @51
    sseq12d
    @50
    @20
    @11
    @14
    @4
    @50
    @19
    @10
    cid
    @50
    @17
    @8
    @18
    @9
    @14
    @4
    dmeq
    @14
    @4
    rneq
    uneq12d
    reseq2d
    @51
    sseq12d
    anbi12d
    cleq2lem
    spcev
    @23
    vx
    intexab
    sylib
    mp2an
end
