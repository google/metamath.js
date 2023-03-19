include "wlim.mm"
include "cv.mm"
include "wss.mm"
include "ccf.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "csuc.mm"
include "ciun.mm"
include "wrex.mm"
include "cab.mm"
include "cdom.mm"
include "wn.mm"
include "wi.mm"
include "con0.mm"
include "word.mm"
include "limord.mm"
include "ordsson.mm"
include "sstr.mm"
include "expcom.mm"
include "3syl.mm"
include "onsucuni.mm"
include "syl6.mm"
include "adantrd.mm"
include "ralimdv.mm"
include "uniiun.mm"
include "ss2iun.mm"
include "syl5eqss.mm"
include "imp.mm"
include "wcel.mm"
include "cfslbn.mm"
include "3expib.mm"
include "ordsucss.mm"
include "sylsyld.mm"
include "iunss.mm"
include "syl6ibr.mm"
include "sseq1.mm"
include "eqss.mm"
include "simplbi2com.mm"
include "syl6bi.mm"
include "com3l.mm"
include "sylc.mm"
include "limsuc.mm"
include "sylibd.mm"
include "r19.29.mm"
include "eleq1.mm"
include "biimparc.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "abssdv.mm"
include "vuniex.mm"
include "sucex.mm"
include "dfiun2.mm"
include "eqeq1i.mm"
include "cfslb.mm"
include "3expia.mm"
include "syl5bi.mm"
include "syldan.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "wfo.mm"
include "wfn.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "cvv.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "breq1.mm"
include "foeq2.mm"
include "breq2.mm"
include "imbi12d.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfon.mm"
include "sdomdom.mm"
include "ondomen.mm"
include "sylancr.mm"
include "fodomnum.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "mpi.mm"
include "syl5eqbrr.mm"
include "domtr.mm"
include "sylan2.mm"
include "domnsym.mm"
include "pm2.01da.mm"
include "a1i.mm"
include "3syld.mm"
include "necon2ad.mm"

theorem cfslb2n
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume cfslb.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ( Lim A /\ A. x e. B ( x C_ A /\ x ~< ( cf ` A ) ) ) -> ( B ~< ( cf ` A ) -> U. B =/= A ) )

  proof
    cA
    wlim
    #
    vx
    cv
    #
    cA
    wss
    #
    @1
    cA
    ccf
    cfv
    #
    csdm
    wbr
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    #
    cB
    @3
    csdm
    wbr
    #
    cB
    cuni
    #
    cA
    @7
    @9
    cA
    wceq
    #
    vx
    cB
    @1
    cuni
    #
    csuc
    #
    ciun
    #
    cA
    wceq
    #
    @3
    vy
    cv
    #
    @12
    wceq
    #
    vx
    cB
    wrex
    #
    vy
    cab
    #
    cdom
    wbr
    #
    @8
    wn
    #
    @7
    @9
    @13
    wss
    #
    @13
    cA
    wss
    #
    @10
    @14
    wi
    @0
    @6
    @21
    @0
    @6
    @1
    @12
    wss
    #
    vx
    cB
    wral
    #
    @21
    @0
    @5
    @23
    vx
    cB
    @0
    @2
    @23
    @4
    @0
    @2
    @1
    con0
    wss
    #
    @23
    @0
    cA
    word
    #
    cA
    con0
    wss
    #
    @2
    @25
    wi
    cA
    limord
    #
    cA
    ordsson
    @2
    @27
    @25
    @1
    cA
    con0
    sstr
    expcom
    3syl
    @1
    onsucuni
    syl6
    adantrd
    ralimdv
    @24
    @9
    vx
    cB
    @1
    ciun
    @13
    vx
    cB
    uniiun
    vx
    cB
    @1
    @12
    ss2iun
    syl5eqss
    syl6
    imp
    @0
    @6
    @22
    @0
    @6
    @12
    cA
    wss
    #
    vx
    cB
    wral
    @22
    @0
    @5
    @29
    vx
    cB
    @0
    @26
    @5
    @11
    cA
    wcel
    #
    @29
    @28
    @0
    @2
    @4
    @30
    cA
    @1
    cfslb.1
    cfslbn
    3expib
    #
    @11
    cA
    ordsucss
    sylsyld
    ralimdv
    vx
    cB
    @12
    cA
    iunss
    syl6ibr
    imp
    @10
    @21
    @22
    @14
    @10
    @21
    cA
    @13
    wss
    #
    @22
    @14
    wi
    @9
    cA
    @13
    sseq1
    @14
    @22
    @32
    @13
    cA
    eqss
    simplbi2com
    syl6bi
    com3l
    sylc
    @0
    @6
    @18
    cA
    wss
    #
    @14
    @19
    wi
    @7
    @17
    vy
    cA
    @7
    @12
    cA
    wcel
    #
    vx
    cB
    wral
    #
    @17
    @15
    cA
    wcel
    #
    wi
    @0
    @6
    @35
    @0
    @5
    @34
    vx
    cB
    @0
    @5
    @30
    @34
    @31
    cA
    @11
    limsuc
    sylibd
    ralimdv
    imp
    @35
    @17
    @36
    @35
    @17
    wa
    @34
    @16
    wa
    #
    vx
    cB
    wrex
    @36
    @34
    @16
    vx
    cB
    r19.29
    @37
    @36
    vx
    cB
    @16
    @36
    @34
    @15
    @12
    cA
    eleq1
    biimparc
    rexlimivw
    syl
    ex
    syl
    abssdv
    @14
    @18
    cuni
    #
    cA
    wceq
    #
    @0
    @33
    wa
    @19
    @13
    @38
    cA
    vx
    vy
    cB
    @12
    @11
    vx
    vuniex
    sucex
    #
    dfiun2
    eqeq1i
    @0
    @33
    @39
    @19
    cA
    @18
    cfslb.1
    cfslb
    3expia
    syl5bi
    syldan
    @19
    @20
    wi
    @7
    @19
    @8
    @19
    @8
    wa
    @3
    cB
    cdom
    wbr
    #
    @20
    @8
    @19
    @18
    cB
    cdom
    wbr
    @41
    @8
    @18
    vx
    cB
    @12
    cmpt
    #
    crn
    #
    cB
    cdom
    vx
    vy
    cB
    @12
    @42
    @42
    eqid
    #
    rnmpt
    @8
    cB
    @43
    @42
    wfo
    #
    @43
    cB
    cdom
    wbr
    #
    @42
    cB
    wfn
    @45
    vx
    cB
    @12
    @42
    @40
    @44
    fnmpti
    cB
    @42
    dffn4
    mpbi
    cB
    cvv
    wcel
    @8
    @45
    @46
    wi
    #
    cB
    @3
    csdm
    relsdom
    brrelexi
    @15
    @3
    csdm
    wbr
    #
    @15
    @43
    @42
    wfo
    #
    @43
    @15
    cdom
    wbr
    #
    wi
    #
    wi
    @8
    @47
    wi
    vy
    cB
    cvv
    @15
    cB
    wceq
    #
    @48
    @8
    @51
    @47
    @15
    cB
    @3
    csdm
    breq1
    @52
    @49
    @45
    @50
    @46
    @15
    cB
    @43
    @42
    foeq2
    @15
    cB
    @43
    cdom
    breq2
    imbi12d
    imbi12d
    @48
    @15
    ccrd
    cdm
    wcel
    #
    @51
    @48
    @3
    con0
    wcel
    @15
    @3
    cdom
    wbr
    @53
    cA
    cfon
    @15
    @3
    sdomdom
    @3
    @15
    ondomen
    sylancr
    @15
    @43
    @42
    fodomnum
    syl
    vtoclg
    mpcom
    mpi
    syl5eqbrr
    @3
    @18
    cB
    domtr
    sylan2
    @3
    cB
    domnsym
    syl
    pm2.01da
    a1i
    3syld
    necon2ad
end
