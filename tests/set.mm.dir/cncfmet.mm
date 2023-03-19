include "cc.mm"
include "wss.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wf.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cmin.mm"
include "cabs.mm"
include "wcel.mm"
include "wb.mm"
include "wceq.mm"
include "simplll.mm"
include "simprl.mm"
include "simprr.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "ad2ant2l.mm"
include "ssel2.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "syl22anc.mm"
include "breq1d.mm"
include "ffvelrn.mm"
include "ad2ant2lr.mm"
include "syl2anc.mm"
include "simpllr.mm"
include "sseldd.mm"
include "imbi12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "mpan.mm"
include "syl5eqel.mm"
include "metcn.mm"
include "elcncf.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem cncfmet
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cncfmet.1: |- C = ( ( abs o. - ) |` ( A X. A ) )
  assume cncfmet.2: |- D = ( ( abs o. - ) |` ( B X. B ) )
  assume cncfmet.3: |- J = ( MetOpen ` C )
  assume cncfmet.4: |- K = ( MetOpen ` D )


  assert |- ( ( A C_ CC /\ B C_ CC ) -> ( A -cn-> B ) = ( J Cn K ) )

  proof
    cA
    cc
    wss
    #
    cB
    cc
    wss
    #
    wa
    #
    vf
    cA
    cB
    ccncf
    co
    #
    cJ
    cK
    ccn
    co
    #
    @2
    cA
    cB
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cC
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    @7
    @5
    cfv
    #
    @8
    @5
    cfv
    #
    cD
    co
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    @6
    @7
    @8
    cmin
    co
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    @12
    @13
    cmin
    co
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    wa
    @5
    @4
    wcel
    #
    @5
    @3
    wcel
    @2
    @6
    @21
    @31
    @2
    @6
    wa
    #
    @20
    @30
    vx
    cA
    @33
    @7
    cA
    wcel
    #
    wa
    #
    @19
    @29
    vy
    crp
    @35
    @18
    @28
    vz
    crp
    @35
    @17
    @27
    vw
    cA
    @33
    @34
    @8
    cA
    wcel
    #
    @17
    @27
    wb
    @33
    @34
    @36
    wa
    #
    wa
    #
    @11
    @24
    @16
    @26
    @38
    @9
    @23
    @10
    clt
    @38
    @0
    @34
    @0
    @36
    @9
    @23
    wceq
    @0
    @1
    @6
    @37
    simplll
    #
    @33
    @34
    @36
    simprl
    @39
    @33
    @34
    @36
    simprr
    @0
    @34
    wa
    #
    @0
    @36
    wa
    #
    wa
    @9
    @7
    @8
    cabs
    cmin
    ccom
    #
    co
    #
    @23
    @34
    @36
    @9
    @43
    wceq
    @0
    @0
    @37
    @9
    @7
    @8
    @42
    cA
    cA
    cxp
    cres
    #
    co
    @43
    cC
    @44
    @7
    @8
    cncfmet.1
    oveqi
    @7
    @8
    cA
    cA
    @42
    ovres
    syl5eq
    ad2ant2l
    @40
    @7
    cc
    wcel
    @8
    cc
    wcel
    @43
    @23
    wceq
    @41
    cA
    cc
    @7
    ssel2
    cA
    cc
    @8
    ssel2
    @7
    @8
    @42
    @42
    eqid
    #
    cnmetdval
    syl2an
    eqtrd
    syl22anc
    breq1d
    @38
    @14
    @25
    @15
    clt
    @38
    @14
    @12
    @13
    @42
    co
    #
    @25
    @38
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @14
    @46
    wceq
    @6
    @34
    @47
    @2
    @36
    cA
    cB
    @7
    @5
    ffvelrn
    ad2ant2lr
    #
    @6
    @36
    @48
    @2
    @34
    cA
    cB
    @8
    @5
    ffvelrn
    ad2ant2l
    #
    @47
    @48
    wa
    @14
    @12
    @13
    @42
    cB
    cB
    cxp
    cres
    #
    co
    @46
    cD
    @51
    @12
    @13
    cncfmet.2
    oveqi
    @12
    @13
    cB
    cB
    @42
    ovres
    syl5eq
    syl2anc
    @38
    @12
    cc
    wcel
    @13
    cc
    wcel
    @46
    @25
    wceq
    @38
    cB
    cc
    @12
    @0
    @1
    @6
    @37
    simpllr
    #
    @49
    sseldd
    @38
    cB
    cc
    @13
    @52
    @50
    sseldd
    @12
    @13
    @42
    @45
    cnmetdval
    syl2anc
    eqtrd
    breq1d
    imbi12d
    anassrs
    ralbidva
    rexbidv
    ralbidv
    ralbidva
    pm5.32da
    @0
    cC
    cA
    cxmt
    cfv
    #
    wcel
    cD
    cB
    cxmt
    cfv
    #
    wcel
    @32
    @22
    wb
    @1
    @0
    cC
    @44
    @53
    cncfmet.1
    @42
    cc
    cxmt
    cfv
    wcel
    #
    @0
    @44
    @53
    wcel
    cnxmet
    @42
    cA
    cc
    xmetres2
    mpan
    syl5eqel
    @1
    cD
    @51
    @54
    cncfmet.2
    @55
    @1
    @51
    @54
    wcel
    cnxmet
    @42
    cB
    cc
    xmetres2
    mpan
    syl5eqel
    vx
    vy
    vz
    vw
    cC
    cD
    @5
    cJ
    cK
    cA
    cB
    cncfmet.3
    cncfmet.4
    metcn
    syl2an
    vx
    vy
    vz
    vw
    cA
    cB
    @5
    elcncf
    3bitr4rd
    eqrdv
end
