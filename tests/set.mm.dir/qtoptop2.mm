include "ctop.mm"
include "wcel.mm"
include "wfun.mm"
include "w3a.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "eqid.mm"
include "qtopres.mm"
include "3ad2ant2.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "crn.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "cpw.mm"
include "cdm.mm"
include "wfo.mm"
include "wb.mm"
include "simp1.mm"
include "funres.mm"
include "3ad2ant3.mm"
include "funforn.mm"
include "sylib.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "a1i.mm"
include "elqtop.mm"
include "syl3anc.mm"
include "simprbda.mm"
include "selpw.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "sstr2.mm"
include "syl5com.mm"
include "sspwuni.mm"
include "syl6ib.mm"
include "ciun.mm"
include "imauni.mm"
include "simpl1.mm"
include "simplbda.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "mpan9.mm"
include "iunopn.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "jcad.mm"
include "sylibrd.mm"
include "alrimiv.mm"
include "biimpa.mm"
include "adantrr.mm"
include "simpld.mm"
include "syl5ss.mm"
include "adantr.mm"
include "inpreima.mm"
include "syl.mm"
include "simprd.mm"
include "adantrl.mm"
include "inopn.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "ovex.mm"
include "istopg.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem qtoptop2
  let cF: class F
  let cJ: class J
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. Top /\ F e. V /\ Fun F ) -> ( J qTop F ) e. Top )

  proof
    cJ
    ctop
    wcel
    #
    cF
    cV
    wcel
    #
    cF
    wfun
    #
    w3a
    #
    cJ
    cF
    cqtop
    co
    #
    cJ
    cF
    cJ
    cuni
    #
    cres
    #
    cqtop
    co
    #
    ctop
    @1
    @0
    @4
    @7
    wceq
    @2
    cF
    cJ
    cV
    @5
    @5
    eqid
    #
    qtopres
    3ad2ant2
    @3
    vx
    cv
    #
    @7
    wss
    #
    @9
    cuni
    #
    @7
    wcel
    #
    wi
    #
    vx
    wal
    #
    @9
    vy
    cv
    #
    cin
    #
    @7
    wcel
    #
    vy
    @7
    wral
    vx
    @7
    wral
    #
    @7
    ctop
    wcel
    #
    @3
    @13
    vx
    @3
    @10
    @11
    @6
    crn
    #
    wss
    #
    @6
    ccnv
    #
    @11
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @12
    @3
    @10
    @21
    @24
    @3
    @10
    @9
    @20
    cpw
    #
    wss
    #
    @21
    @3
    @7
    @26
    wss
    @10
    @27
    @3
    vy
    @7
    @26
    @3
    @15
    @7
    wcel
    #
    @15
    @26
    wcel
    #
    @3
    @28
    wa
    @15
    @20
    wss
    #
    @29
    @3
    @28
    @30
    @22
    @15
    cima
    #
    cJ
    wcel
    #
    @3
    @0
    @6
    cdm
    #
    @20
    @6
    wfo
    #
    @33
    @5
    wss
    #
    @28
    @30
    @32
    wa
    wb
    @0
    @1
    @2
    simp1
    #
    @3
    @6
    wfun
    #
    @34
    @2
    @0
    @37
    @1
    @5
    cF
    funres
    3ad2ant3
    #
    @6
    funforn
    sylib
    #
    @35
    @3
    @33
    @5
    cF
    cdm
    #
    cin
    @5
    cF
    @5
    dmres
    @5
    @40
    inss1
    eqsstri
    a1i
    #
    @15
    @6
    cJ
    ctop
    @5
    @20
    @33
    @8
    elqtop
    syl3anc
    #
    simprbda
    vy
    @20
    selpw
    sylibr
    ex
    ssrdv
    @9
    @7
    @26
    sstr2
    syl5com
    @9
    @20
    sspwuni
    syl6ib
    @3
    @10
    @24
    @3
    @10
    wa
    #
    @23
    vy
    @9
    @31
    ciun
    #
    cJ
    vy
    @22
    @9
    imauni
    @43
    @0
    @32
    vy
    @9
    wral
    #
    @44
    cJ
    wcel
    @0
    @1
    @2
    @10
    simpl1
    @3
    @32
    vy
    @7
    wral
    @10
    @45
    @3
    @32
    vy
    @7
    @3
    @28
    @30
    @32
    @42
    simplbda
    #
    ralrimiva
    @32
    vy
    @9
    @7
    ssralv
    mpan9
    vy
    @9
    @31
    cJ
    iunopn
    syl2anc
    syl5eqel
    ex
    jcad
    @3
    @0
    @34
    @35
    @12
    @25
    wb
    @36
    @39
    @41
    @11
    @6
    cJ
    ctop
    @5
    @20
    @33
    @8
    elqtop
    syl3anc
    sylibrd
    alrimiv
    @3
    @17
    vx
    vy
    @7
    @7
    @3
    @9
    @7
    wcel
    #
    @28
    wa
    #
    wa
    #
    @17
    @16
    @20
    wss
    #
    @22
    @16
    cima
    #
    cJ
    wcel
    #
    @49
    @16
    @9
    @20
    @9
    @15
    inss1
    @49
    @9
    @20
    wss
    #
    @22
    @9
    cima
    #
    cJ
    wcel
    #
    @3
    @47
    @53
    @55
    wa
    #
    @28
    @3
    @47
    @56
    @3
    @0
    @34
    @35
    @47
    @56
    wb
    @36
    @39
    @41
    @9
    @6
    cJ
    ctop
    @5
    @20
    @33
    @8
    elqtop
    syl3anc
    biimpa
    adantrr
    #
    simpld
    syl5ss
    @49
    @51
    @54
    @31
    cin
    #
    cJ
    @49
    @37
    @51
    @58
    wceq
    @3
    @37
    @48
    @38
    adantr
    @9
    @15
    @6
    inpreima
    syl
    @49
    @0
    @55
    @32
    @58
    cJ
    wcel
    @3
    @0
    @48
    @36
    adantr
    @49
    @53
    @55
    @57
    simprd
    @3
    @28
    @32
    @47
    @46
    adantrl
    @54
    @31
    cJ
    inopn
    syl3anc
    eqeltrd
    @3
    @17
    @50
    @52
    wa
    wb
    #
    @48
    @3
    @0
    @34
    @35
    @59
    @36
    @39
    @41
    @16
    @6
    cJ
    ctop
    @5
    @20
    @33
    @8
    elqtop
    syl3anc
    adantr
    mpbir2and
    ralrimivva
    @7
    cvv
    wcel
    @19
    @14
    @18
    wa
    wb
    cJ
    @6
    cqtop
    ovex
    vx
    vy
    cvv
    @7
    istopg
    ax-mp
    sylanbrc
    eqeltrd
end
