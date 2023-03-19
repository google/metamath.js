include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cabs.mm"
include "cfv.mm"
include "cno.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "fveq2.mm"
include "abs0.mm"
include "chil.mm"
include "wcel.mm"
include "normge0.mm"
include "ax-mp.mm"
include "normcli.mm"
include "mulge0i.mm"
include "mp2an.mm"
include "eqbrtri.mm"
include "syl6eqbr.mm"
include "wn.mm"
include "c2.mm"
include "csqrt.mm"
include "wne.mm"
include "df-ne.mm"
include "cdiv.mm"
include "ccj.mm"
include "caddc.mm"
include "his1i.mm"
include "oveq2i.mm"
include "cc.mm"
include "hicli.mm"
include "abslem2.mm"
include "mpan.mm"
include "syl5req.mm"
include "c1.mm"
include "wa.mm"
include "abs00i.mm"
include "necon3bii.mm"
include "abscli.mm"
include "recni.mm"
include "divclzi.mm"
include "divreczi.mm"
include "fveq2d.mm"
include "recclzi.mm"
include "absmul.mm"
include "sylancr.mm"
include "rerecclzi.mm"
include "cr.mm"
include "clt.mm"
include "0re.mm"
include "jctil.mm"
include "absgt0i.mm"
include "bitri.mm"
include "recgt0i.mm"
include "sylbi.mm"
include "ltle.mm"
include "sylc.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "recidzi.mm"
include "3eqtrd.mm"
include "jca.mm"
include "sylbir.mm"
include "normlem7tALT.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "normval.mm"
include "oveq12i.mm"
include "mulcomli.mm"
include "breq2i.mm"
include "wb.mm"
include "2pos.mm"
include "hiidge0.mm"
include "hiidrcl.mm"
include "sqrtcli.mm"
include "mp2b.mm"
include "remulcli.mm"
include "2re.mm"
include "lemul2i.mm"
include "sylibr.mm"
include "pm2.61i.mm"

theorem bcsiALT
  let cA: class A
  let cB: class B
  assume bcs.1: |- A e. ~H
  assume bcs.2: |- B e. ~H


  assert |- ( abs ` ( A .ih B ) ) <_ ( ( normh ` A ) x. ( normh ` B ) )

  proof
    cA
    cB
    csp
    co
    #
    cc0
    wceq
    #
    @0
    cabs
    cfv
    #
    cA
    cno
    cfv
    #
    cB
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @1
    @2
    cc0
    cabs
    cfv
    #
    @5
    cle
    @0
    cc0
    cabs
    fveq2
    @7
    cc0
    @5
    cle
    abs0
    cc0
    @3
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    cA
    chil
    wcel
    #
    @8
    bcs.1
    cA
    normge0
    ax-mp
    cB
    chil
    wcel
    #
    @9
    bcs.2
    cB
    normge0
    ax-mp
    @3
    @4
    cA
    bcs.1
    normcli
    #
    cB
    bcs.2
    normcli
    #
    mulge0i
    mp2an
    eqbrtri
    syl6eqbr
    @1
    wn
    #
    c2
    @2
    cmul
    co
    #
    c2
    cB
    cB
    csp
    co
    #
    csqrt
    cfv
    #
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    @6
    @14
    @0
    cc0
    wne
    #
    @22
    @0
    cc0
    df-ne
    @23
    @15
    @0
    @2
    cdiv
    co
    #
    ccj
    cfv
    @0
    cmul
    co
    #
    @24
    cB
    cA
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @21
    cle
    @23
    @28
    @25
    @24
    @0
    ccj
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @15
    @27
    @30
    @25
    caddc
    @26
    @29
    @24
    cmul
    cB
    cA
    bcs.2
    bcs.1
    his1i
    oveq2i
    oveq2i
    @0
    cc
    wcel
    #
    @23
    @31
    @15
    wceq
    cA
    cB
    bcs.1
    bcs.2
    hicli
    #
    @0
    abslem2
    mpan
    syl5req
    @23
    @24
    cc
    wcel
    #
    @24
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @28
    @21
    cle
    wbr
    @23
    @2
    cc0
    wne
    #
    @37
    @2
    cc0
    @0
    cc0
    @0
    @33
    abs00i
    necon3bii
    #
    @38
    @34
    @36
    @0
    @2
    @33
    @2
    @0
    @33
    abscli
    #
    recni
    #
    divclzi
    @38
    @35
    @0
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @2
    @42
    cmul
    co
    #
    c1
    @38
    @24
    @43
    cabs
    @0
    @2
    @33
    @41
    divreczi
    fveq2d
    @38
    @44
    @2
    @42
    cabs
    cfv
    #
    cmul
    co
    #
    @45
    @38
    @32
    @42
    cc
    wcel
    @44
    @47
    wceq
    @33
    @2
    @41
    recclzi
    @0
    @42
    absmul
    sylancr
    @38
    @46
    @42
    @2
    cmul
    @38
    @42
    @2
    @40
    rerecclzi
    #
    @38
    cc0
    cr
    wcel
    #
    @42
    cr
    wcel
    #
    wa
    cc0
    @42
    clt
    wbr
    #
    cc0
    @42
    cle
    wbr
    @38
    @50
    @49
    @48
    0re
    jctil
    @38
    cc0
    @2
    clt
    wbr
    #
    @51
    @38
    @23
    @52
    @39
    @0
    @33
    absgt0i
    bitri
    @2
    @40
    recgt0i
    sylbi
    cc0
    @42
    ltle
    sylc
    absidd
    oveq2d
    eqtrd
    @2
    @41
    recidzi
    3eqtrd
    jca
    sylbir
    cA
    cB
    @24
    bcs.1
    bcs.2
    normlem7tALT
    syl
    eqbrtrd
    sylbir
    @6
    @2
    @20
    cle
    wbr
    #
    @22
    @5
    @20
    @2
    cle
    @4
    @3
    @20
    @4
    @13
    recni
    @3
    @12
    recni
    @4
    @17
    @3
    @19
    cmul
    @11
    @4
    @17
    wceq
    bcs.2
    cB
    normval
    ax-mp
    @10
    @3
    @19
    wceq
    bcs.1
    cA
    normval
    ax-mp
    oveq12i
    mulcomli
    breq2i
    cc0
    c2
    clt
    wbr
    @53
    @22
    wb
    2pos
    @2
    @20
    c2
    @40
    @17
    @19
    @11
    cc0
    @16
    cle
    wbr
    @17
    cr
    wcel
    bcs.2
    cB
    hiidge0
    @16
    @11
    @16
    cr
    wcel
    bcs.2
    cB
    hiidrcl
    ax-mp
    sqrtcli
    mp2b
    @10
    cc0
    @18
    cle
    wbr
    @19
    cr
    wcel
    bcs.1
    cA
    hiidge0
    @18
    @10
    @18
    cr
    wcel
    bcs.1
    cA
    hiidrcl
    ax-mp
    sqrtcli
    mp2b
    remulcli
    2re
    lemul2i
    ax-mp
    bitri
    sylibr
    pm2.61i
end
