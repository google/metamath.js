include "cc0.mm"
include "wceq.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wa.mm"
include "wn.mm"
include "cgcd.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "cz.mm"
include "wcel.mm"
include "gcddvds.mm"
include "mp2an.mm"
include "simpli.mm"
include "c1.mm"
include "wi.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0zi.mm"
include "w3a.mm"
include "1z.mm"
include "dvds2ln.mm"
include "mpanl12.mm"
include "mp3an.mm"
include "ax-mp.mm"
include "cc.mm"
include "zcn.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "breqtri.mm"
include "zmulcl.mm"
include "zaddcl.mm"
include "dvdslegcd.mm"
include "ex.mm"
include "mp2ani.mm"
include "cneg.mm"
include "znegcl.mm"
include "mulneg1i.mm"
include "oveq12i.mm"
include "mulcli.mm"
include "negcli.mm"
include "negidi.mm"
include "addcomli.mm"
include "oveq1i.mm"
include "addassi.mm"
include "addid2i.mm"
include "3eqtr3i.mm"
include "eqtri.mm"
include "anim12i.mm"
include "zrei.mm"
include "letri3i.mm"
include "sylibr.mm"
include "wo.mm"
include "pm4.57.mm"
include "oveq2.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "pm5.32i.mm"
include "oveq12.mm"
include "sylbir.mm"
include "eqtr4d.mm"
include "sylbi.mm"
include "jaoi.mm"
include "pm2.61i.mm"

theorem gcdaddmlem
  let cK: class K
  let cM: class M
  let cN: class N
  assume gcdaddmlem.1: |- K e. ZZ
  assume gcdaddmlem.2: |- M e. ZZ
  assume gcdaddmlem.3: |- N e. ZZ


  assert |- ( M gcd N ) = ( M gcd ( ( K x. M ) + N ) )

  proof
    cM
    cc0
    wceq
    #
    cK
    cM
    cmul
    co
    #
    cN
    caddc
    co
    #
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @0
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    @2
    cgcd
    co
    #
    wceq
    #
    @9
    @10
    @11
    cle
    wbr
    #
    @11
    @10
    cle
    wbr
    #
    wa
    @12
    @5
    @13
    @8
    @14
    @5
    @10
    cM
    cdvds
    wbr
    #
    @10
    @2
    cdvds
    wbr
    #
    @13
    @15
    @10
    cN
    cdvds
    wbr
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @15
    @17
    wa
    #
    gcdaddmlem.2
    gcdaddmlem.3
    cM
    cN
    gcddvds
    mp2an
    #
    simpli
    @10
    @1
    c1
    cN
    cmul
    co
    #
    caddc
    co
    #
    @2
    cdvds
    @20
    @10
    @23
    cdvds
    wbr
    #
    @21
    @10
    cz
    wcel
    #
    @18
    @19
    @20
    @24
    wi
    #
    @10
    @18
    @19
    @10
    cn0
    wcel
    gcdaddmlem.2
    gcdaddmlem.3
    cM
    cN
    gcdcl
    mp2an
    nn0zi
    #
    gcdaddmlem.2
    gcdaddmlem.3
    cK
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @25
    @18
    @19
    w3a
    @26
    gcdaddmlem.1
    1z
    cK
    c1
    @10
    cM
    cN
    dvds2ln
    mpanl12
    mp3an
    ax-mp
    @22
    cN
    @1
    caddc
    cN
    @19
    cN
    cc
    wcel
    gcdaddmlem.3
    cN
    zcn
    ax-mp
    #
    mulid2i
    oveq2i
    breqtri
    @25
    @18
    @2
    cz
    wcel
    #
    @5
    @15
    @16
    wa
    @13
    wi
    #
    wi
    @27
    gcdaddmlem.2
    @1
    cz
    wcel
    #
    @19
    @31
    @28
    @18
    @33
    gcdaddmlem.1
    gcdaddmlem.2
    cK
    cM
    zmulcl
    mp2an
    gcdaddmlem.3
    @1
    cN
    zaddcl
    mp2an
    #
    @25
    @18
    @31
    w3a
    @5
    @32
    @10
    cM
    @2
    dvdslegcd
    ex
    mp3an
    mp2ani
    @8
    @11
    cM
    cdvds
    wbr
    #
    @11
    cN
    cdvds
    wbr
    #
    @14
    @35
    @11
    @2
    cdvds
    wbr
    #
    @18
    @31
    @35
    @37
    wa
    #
    gcdaddmlem.2
    @34
    cM
    @2
    gcddvds
    mp2an
    #
    simpli
    @11
    cK
    cneg
    #
    cM
    cmul
    co
    #
    c1
    @2
    cmul
    co
    #
    caddc
    co
    #
    cN
    cdvds
    @38
    @11
    @43
    cdvds
    wbr
    #
    @39
    @11
    cz
    wcel
    #
    @18
    @31
    @38
    @44
    wi
    #
    @11
    @18
    @31
    @11
    cn0
    wcel
    gcdaddmlem.2
    @34
    cM
    @2
    gcdcl
    mp2an
    nn0zi
    #
    gcdaddmlem.2
    @34
    @40
    cz
    wcel
    #
    @29
    @45
    @18
    @31
    w3a
    @46
    @28
    @48
    gcdaddmlem.1
    cK
    znegcl
    ax-mp
    1z
    @40
    c1
    @11
    cM
    @2
    dvds2ln
    mpanl12
    mp3an
    ax-mp
    @43
    @1
    cneg
    #
    @2
    caddc
    co
    #
    cN
    @41
    @49
    @42
    @2
    caddc
    cK
    cM
    @28
    cK
    cc
    wcel
    gcdaddmlem.1
    cK
    zcn
    ax-mp
    #
    @18
    cM
    cc
    wcel
    gcdaddmlem.2
    cM
    zcn
    ax-mp
    #
    mulneg1i
    @2
    @31
    @2
    cc
    wcel
    @34
    @2
    zcn
    ax-mp
    mulid2i
    oveq12i
    @49
    @1
    caddc
    co
    #
    cN
    caddc
    co
    cc0
    cN
    caddc
    co
    #
    @50
    cN
    @53
    cc0
    cN
    caddc
    @1
    @49
    cc0
    cK
    cM
    @51
    @52
    mulcli
    #
    @1
    @55
    negcli
    #
    @1
    @55
    negidi
    addcomli
    oveq1i
    @49
    @1
    cN
    @56
    @55
    @30
    addassi
    cN
    @30
    addid2i
    #
    3eqtr3i
    eqtri
    breqtri
    @45
    @18
    @19
    @8
    @35
    @36
    wa
    @14
    wi
    #
    wi
    @47
    gcdaddmlem.2
    gcdaddmlem.3
    @45
    @18
    @19
    w3a
    @8
    @58
    @11
    cM
    cN
    dvdslegcd
    ex
    mp3an
    mp2ani
    anim12i
    @10
    @11
    @10
    @27
    zrei
    @11
    @47
    zrei
    letri3i
    sylibr
    @9
    wn
    @4
    @7
    wo
    @12
    @4
    @7
    pm4.57
    @4
    @12
    @7
    @4
    @7
    @12
    @0
    @3
    @6
    @0
    @2
    cN
    cc0
    @0
    @2
    @54
    cN
    @0
    @1
    cc0
    cN
    caddc
    @0
    @1
    cK
    cc0
    cmul
    co
    cc0
    cM
    cc0
    cK
    cmul
    oveq2
    cK
    @51
    mul01i
    syl6eq
    oveq1d
    @57
    syl6eq
    eqeq1d
    pm5.32i
    #
    @7
    @10
    cc0
    cc0
    cgcd
    co
    #
    @11
    cM
    cc0
    cN
    cc0
    cgcd
    oveq12
    @7
    @4
    @11
    @60
    wceq
    @59
    cM
    cc0
    @2
    cc0
    cgcd
    oveq12
    sylbir
    eqtr4d
    #
    sylbi
    @61
    jaoi
    sylbi
    pm2.61i
end
