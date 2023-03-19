include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "csiga.mm"
include "cfv.mm"
include "0elpw.mm"
include "pwidg.mm"
include "prssi.mm"
include "sylancr.mm"
include "prid2g.mm"
include "dif0.mm"
include "syl5eqel.mm"
include "difid.mm"
include "0ex.mm"
include "prid1.mm"
include "a1i.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "ralprg.mm"
include "mpan.mm"
include "mpbir2and.mm"
include "csn.mm"
include "cun.mm"
include "uni0.mm"
include "eqeltri.mm"
include "unisn.mm"
include "pm3.2i.mm"
include "snex.mm"
include "unieq.mm"
include "mp1i.mm"
include "mpbiri.mm"
include "unisng.mm"
include "eqeltrd.mm"
include "uniprg.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "prex.mm"
include "ralun.mm"
include "syl2anc.mm"
include "pwpr.mm"
include "raleqi.mm"
include "sylibr.mm"
include "ax-1.mm"
include "ralimi.mm"
include "syl.mm"
include "3jca.mm"
include "issiga.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem prsiga
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( O e. V -> { (/) , O } e. ( sigAlgebra ` O ) )

  proof
    cO
    cV
    wcel
    #
    c0
    cO
    cpr
    #
    cO
    cpw
    #
    wss
    #
    cO
    @1
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @1
    wcel
    #
    vx
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    #
    @5
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    w3a
    #
    @1
    cO
    csiga
    cfv
    wcel
    #
    @0
    c0
    @2
    wcel
    cO
    @2
    wcel
    @3
    cO
    0elpw
    cO
    cV
    pwidg
    c0
    cO
    @2
    prssi
    sylancr
    @0
    @4
    @8
    @14
    c0
    cO
    cV
    prid2g
    #
    @0
    @8
    cO
    c0
    cdif
    #
    @1
    wcel
    #
    cO
    cO
    cdif
    #
    @1
    wcel
    #
    @0
    @18
    cO
    @1
    cO
    dif0
    @17
    syl5eqel
    @0
    @20
    c0
    @1
    cO
    difid
    c0
    @1
    wcel
    @0
    c0
    cO
    0ex
    prid1
    #
    a1i
    syl5eqel
    c0
    cvv
    wcel
    #
    @0
    @8
    @19
    @21
    wa
    wb
    0ex
    @7
    @19
    @21
    vx
    c0
    cO
    cvv
    cV
    @5
    c0
    wceq
    #
    @6
    @18
    @1
    @5
    c0
    cO
    difeq2
    eleq1d
    @5
    cO
    wceq
    @6
    @20
    @1
    @5
    cO
    cO
    difeq2
    eleq1d
    ralprg
    mpan
    mpbir2and
    @0
    @11
    vx
    @13
    wral
    #
    @14
    @0
    @11
    vx
    c0
    c0
    csn
    #
    cpr
    #
    cO
    csn
    #
    @1
    cpr
    #
    cun
    #
    wral
    #
    @25
    @0
    @11
    vx
    @27
    wral
    #
    @11
    vx
    @29
    wral
    #
    @31
    @0
    @32
    c0
    cuni
    #
    @1
    wcel
    #
    @26
    cuni
    #
    @1
    wcel
    #
    wa
    #
    @35
    @37
    @34
    c0
    @1
    uni0
    @22
    eqeltri
    @36
    c0
    @1
    c0
    0ex
    unisn
    @22
    eqeltri
    pm3.2i
    @23
    @26
    cvv
    wcel
    #
    wa
    @32
    @38
    wb
    @0
    @23
    @39
    0ex
    c0
    snex
    pm3.2i
    @11
    @35
    @37
    vx
    c0
    @26
    cvv
    cvv
    @24
    @10
    @34
    @1
    @5
    c0
    unieq
    eleq1d
    @5
    @26
    wceq
    @10
    @36
    @1
    @5
    @26
    unieq
    eleq1d
    ralprg
    mp1i
    mpbiri
    @0
    @33
    @28
    cuni
    #
    @1
    wcel
    #
    @1
    cuni
    #
    @1
    wcel
    #
    @0
    @40
    cO
    @1
    cO
    cV
    unisng
    @17
    eqeltrd
    @0
    @42
    cO
    @1
    @0
    @42
    c0
    cO
    cun
    #
    cO
    @23
    @0
    @42
    @44
    wceq
    0ex
    c0
    cO
    cvv
    cV
    uniprg
    mpan
    @44
    cO
    c0
    cun
    cO
    c0
    cO
    uncom
    cO
    un0
    eqtri
    syl6eq
    @17
    eqeltrd
    @28
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    @33
    @41
    @43
    wa
    wb
    @0
    @45
    @46
    cO
    snex
    c0
    cO
    prex
    #
    pm3.2i
    @11
    @41
    @43
    vx
    @28
    @1
    cvv
    cvv
    @5
    @28
    wceq
    @10
    @40
    @1
    @5
    @28
    unieq
    eleq1d
    @5
    @1
    wceq
    @10
    @42
    @1
    @5
    @1
    unieq
    eleq1d
    ralprg
    mp1i
    mpbir2and
    @11
    vx
    @27
    @29
    ralun
    syl2anc
    @11
    vx
    @13
    @30
    c0
    cO
    pwpr
    raleqi
    sylibr
    @11
    @12
    vx
    @13
    @11
    @9
    ax-1
    ralimi
    syl
    3jca
    @46
    @16
    @3
    @15
    wa
    wb
    @47
    vx
    @1
    cO
    issiga
    ax-mp
    sylanbrc
end
