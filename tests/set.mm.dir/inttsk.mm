include "ctsk.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "simpll.mm"
include "sselda.mm"
include "elinti.mm"
include "imp.mm"
include "adantll.mm"
include "tskpwss.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "ssint.mm"
include "sylibr.mm"
include "tskpw.mm"
include "vpwex.mm"
include "elint2.mm"
include "jca.mm"
include "elpwi.mm"
include "wn.mm"
include "wrex.mm"
include "rexnal.mm"
include "cdom.mm"
include "cvv.mm"
include "simpr.mm"
include "intex.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ssdomg.mm"
include "sylc.mm"
include "vex.mm"
include "intss1.mm"
include "ad2antrl.mm"
include "mpsyl.mm"
include "simprr.mm"
include "simplll.mm"
include "simprl.mm"
include "sseldd.mm"
include "sstrd.mm"
include "tsken.mm"
include "ord.mm"
include "mt3d.mm"
include "ensymd.mm"
include "domentr.mm"
include "sbth.mm"
include "rexlimdvaa.mm"
include "syl5bir.mm"
include "con1d.mm"
include "syl6ibr.mm"
include "orrd.mm"
include "sylan2.mm"
include "wb.mm"
include "eltsk2g.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem inttsk
  let cA: class A
  let vt: setvar t
  let vz: setvar z


  assert |- ( ( A C_ Tarski /\ A =/= (/) ) -> |^| A e. Tarski )

  proof
    cA
    ctsk
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cint
    #
    ctsk
    wcel
    #
    vz
    cv
    #
    cpw
    #
    @3
    wss
    #
    @6
    @3
    wcel
    #
    wa
    #
    vz
    @3
    wral
    #
    @5
    @3
    cen
    wbr
    #
    @5
    @3
    wcel
    #
    wo
    #
    vz
    @3
    cpw
    #
    wral
    #
    @2
    @9
    vz
    @3
    @2
    @12
    wa
    #
    @7
    @8
    @16
    @6
    vt
    cv
    #
    wss
    #
    vt
    cA
    wral
    @7
    @16
    @18
    vt
    cA
    @16
    @17
    cA
    wcel
    #
    wa
    #
    @17
    ctsk
    wcel
    #
    @5
    @17
    wcel
    #
    @18
    @16
    cA
    ctsk
    @17
    @0
    @1
    @12
    simpll
    sselda
    #
    @12
    @19
    @22
    @2
    @12
    @19
    @22
    @5
    cA
    @17
    elinti
    imp
    adantll
    #
    @5
    @17
    tskpwss
    syl2anc
    ralrimiva
    vt
    @6
    cA
    ssint
    sylibr
    @16
    @6
    @17
    wcel
    #
    vt
    cA
    wral
    @8
    @16
    @25
    vt
    cA
    @20
    @21
    @22
    @25
    @23
    @24
    @5
    @17
    tskpw
    syl2anc
    ralrimiva
    vt
    @6
    cA
    vz
    vpwex
    elint2
    sylibr
    jca
    ralrimiva
    @2
    @13
    vz
    @14
    @5
    @14
    wcel
    @2
    @5
    @3
    wss
    #
    @13
    @5
    @3
    elpwi
    @2
    @26
    wa
    #
    @11
    @12
    @27
    @11
    wn
    @22
    vt
    cA
    wral
    #
    @12
    @27
    @28
    @11
    @28
    wn
    @22
    wn
    #
    vt
    cA
    wrex
    @27
    @11
    @22
    vt
    cA
    rexnal
    @27
    @29
    @11
    vt
    cA
    @27
    @19
    @29
    wa
    #
    wa
    #
    @5
    @3
    cdom
    wbr
    #
    @3
    @5
    cdom
    wbr
    #
    @11
    @31
    @3
    cvv
    wcel
    #
    @26
    @32
    @2
    @34
    @26
    @30
    @2
    @1
    @34
    @0
    @1
    simpr
    cA
    intex
    sylib
    #
    ad2antrr
    @2
    @26
    @30
    simplr
    #
    @5
    @3
    cvv
    ssdomg
    sylc
    @31
    @3
    @17
    cdom
    wbr
    #
    @17
    @5
    cen
    wbr
    @33
    @17
    cvv
    wcel
    @31
    @3
    @17
    wss
    #
    @37
    vt
    vex
    @19
    @38
    @27
    @29
    @17
    cA
    intss1
    ad2antrl
    #
    @3
    @17
    cvv
    ssdomg
    mpsyl
    @31
    @5
    @17
    @31
    @5
    @17
    cen
    wbr
    #
    @22
    @27
    @19
    @29
    simprr
    @31
    @40
    @22
    @31
    @21
    @5
    @17
    wss
    @40
    @22
    wo
    @31
    cA
    ctsk
    @17
    @0
    @1
    @26
    @30
    simplll
    @27
    @19
    @29
    simprl
    sseldd
    @31
    @5
    @3
    @17
    @36
    @39
    sstrd
    @5
    @17
    tsken
    syl2anc
    ord
    mt3d
    ensymd
    @3
    @17
    @5
    domentr
    syl2anc
    @5
    @3
    sbth
    syl2anc
    rexlimdvaa
    syl5bir
    con1d
    vt
    @5
    cA
    vz
    vex
    elint2
    syl6ibr
    orrd
    sylan2
    ralrimiva
    @2
    @34
    @4
    @10
    @15
    wa
    wb
    @35
    vz
    @3
    cvv
    eltsk2g
    syl
    mpbir2and
end
