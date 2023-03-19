include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "abscl.mm"
include "ralimi.mm"
include "wa.mm"
include "r19.29uz.mm"
include "ex.mm"
include "ralimdv.mm"
include "caubnd2.mm"
include "syl6.mm"
include "cfz.mm"
include "wi.mm"
include "wss.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "cle.mm"
include "cfn.mm"
include "fzfi.mm"
include "fimaxre3.mm"
include "mpan.mm"
include "c1.mm"
include "caddc.mm"
include "peano2re.mm"
include "adantl.mm"
include "ltp1.mm"
include "lelttr.mm"
include "mpd3an3.mm"
include "mpan2d.mm"
include "expcom.mm"
include "impcom.mm"
include "ralim.mm"
include "syl.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wo.mm"
include "cif.mm"
include "w3a.mm"
include "max1.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "ifcl.mm"
include "ancoms.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "max2.mm"
include "simp2.mm"
include "jaod.mm"
include "3expia.mm"
include "syl6d.mm"
include "wal.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseli.mm"
include "uztric.mm"
include "syl2anr.mm"
include "wb.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfzuzb.mm"
include "baib.mm"
include "orbi1d.mm"
include "mpbird.mm"
include "pm3.48.mm"
include "syl9.mm"
include "alimdv.mm"
include "df-ral.mm"
include "anbi12i.mm"
include "19.26.mm"
include "bitr4i.mm"
include "3imtr4g.mm"
include "3impib.mm"
include "imim1i.mm"
include "3expd.mm"
include "com23.mm"
include "expimpd.mm"
include "com3r.mm"
include "com34.mm"
include "rexlimdv.mm"
include "rexlimdvv.mm"
include "sylsyld.mm"
include "imp.mm"

theorem caubnd
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  let cW: class W
  assume cau3.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint j m
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k w
  disjoint k z
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint M w
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint Z w
  disjoint Z z
  disjoint W j
  disjoint W k
  disjoint W x
  assert |- ( ( A. k e. Z ( F ` k ) e. CC /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) -> E. y e. RR A. k e. Z ( abs ` ( F ` k ) ) < y )

  proof
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    cZ
    wral
    #
    @1
    vj
    cv
    #
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @4
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @1
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    vk
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @3
    @10
    cr
    wcel
    #
    vk
    cZ
    wral
    #
    @9
    @10
    vz
    cv
    #
    clt
    wbr
    #
    vk
    @7
    wral
    #
    vj
    cZ
    wrex
    vz
    cr
    wrex
    #
    @14
    @2
    @15
    vk
    cZ
    @1
    abscl
    ralimi
    @3
    @9
    @2
    @6
    wa
    vk
    @7
    wral
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @20
    @3
    @8
    @21
    vx
    crp
    @3
    @8
    @21
    @2
    @6
    vj
    vk
    cM
    cZ
    cau3.1
    r19.29uz
    ex
    ralimdv
    vx
    vz
    vj
    vk
    cF
    cM
    cZ
    cau3.1
    caubnd2
    syl6
    @16
    @19
    @14
    vz
    vj
    cr
    cZ
    @16
    @10
    vw
    cv
    #
    clt
    wbr
    #
    vk
    cM
    @4
    cfz
    co
    #
    wral
    #
    vw
    cr
    wrex
    #
    @17
    cr
    wcel
    #
    @4
    cZ
    wcel
    #
    wa
    #
    @19
    @14
    wi
    #
    wi
    #
    @16
    @15
    vk
    @24
    wral
    #
    @26
    @24
    cZ
    wss
    @16
    @32
    wi
    @24
    cM
    cuz
    cfv
    #
    cZ
    cM
    @4
    fzssuz
    cau3.1
    sseqtr4i
    @15
    vk
    @24
    cZ
    ssralv
    ax-mp
    @32
    @10
    @5
    cle
    wbr
    #
    vk
    @24
    wral
    #
    vx
    cr
    wrex
    #
    @26
    @24
    cfn
    wcel
    @32
    @36
    cM
    @4
    fzfi
    vx
    vk
    @24
    @10
    fimaxre3
    mpan
    @32
    @35
    @26
    vx
    cr
    @32
    @5
    cr
    wcel
    #
    wa
    #
    @5
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @35
    @10
    @39
    clt
    wbr
    #
    vk
    @24
    wral
    #
    @26
    @37
    @40
    @32
    @5
    peano2re
    #
    adantl
    @38
    @34
    @41
    wi
    #
    vk
    @24
    wral
    #
    @35
    @42
    wi
    @37
    @32
    @45
    @37
    @15
    @44
    vk
    @24
    @15
    @37
    @44
    @15
    @37
    wa
    @34
    @5
    @39
    clt
    wbr
    #
    @41
    @37
    @46
    @15
    @5
    ltp1
    adantl
    @15
    @37
    @40
    @34
    @46
    wa
    @41
    wi
    @37
    @40
    @15
    @43
    adantl
    @10
    @5
    @39
    lelttr
    mpd3an3
    mpan2d
    expcom
    ralimdv
    impcom
    @34
    @41
    vk
    @24
    ralim
    syl
    @25
    @42
    vw
    @39
    cr
    @22
    @39
    wceq
    @23
    @41
    vk
    @24
    @22
    @39
    @10
    clt
    breq2
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
    syl
    @16
    @25
    @31
    vw
    cr
    @16
    @22
    cr
    wcel
    #
    @29
    @25
    @30
    @47
    @29
    @16
    @25
    @30
    wi
    #
    @47
    @27
    @28
    @16
    @48
    wi
    @47
    @27
    wa
    #
    @16
    @28
    @48
    @49
    @16
    @23
    @18
    wo
    #
    vk
    cZ
    wral
    #
    @14
    wi
    #
    @28
    @48
    wi
    @49
    @16
    @51
    @10
    @22
    @17
    cle
    wbr
    #
    @17
    @22
    cif
    #
    clt
    wbr
    #
    vk
    cZ
    wral
    #
    @14
    @49
    @16
    @50
    @55
    wi
    #
    vk
    cZ
    wral
    @51
    @56
    wi
    @49
    @15
    @57
    vk
    cZ
    @47
    @27
    @15
    @57
    @47
    @27
    @15
    w3a
    #
    @23
    @55
    @18
    @58
    @23
    @22
    @54
    cle
    wbr
    #
    @55
    @47
    @27
    @59
    @15
    @22
    @17
    max1
    3adant3
    @58
    @15
    @47
    @54
    cr
    wcel
    #
    @23
    @59
    wa
    @55
    wi
    @47
    @27
    @15
    simp3
    #
    @47
    @27
    @15
    simp1
    @47
    @27
    @60
    @15
    @27
    @47
    @60
    @53
    @17
    @22
    cr
    ifcl
    ancoms
    #
    3adant3
    #
    @10
    @22
    @54
    ltletr
    syl3anc
    mpan2d
    @58
    @18
    @17
    @54
    cle
    wbr
    #
    @55
    @47
    @27
    @64
    @15
    @22
    @17
    max2
    3adant3
    @58
    @15
    @27
    @60
    @18
    @64
    wa
    @55
    wi
    @61
    @47
    @27
    @15
    simp2
    @63
    @10
    @17
    @54
    ltletr
    syl3anc
    mpan2d
    jaod
    3expia
    ralimdv
    @50
    @55
    vk
    cZ
    ralim
    syl6
    @49
    @60
    @56
    @14
    wi
    @62
    @60
    @56
    @14
    @13
    @56
    vy
    @54
    cr
    @11
    @54
    wceq
    @12
    @55
    vk
    cZ
    @11
    @54
    @10
    clt
    breq2
    ralbidv
    rspcev
    ex
    syl
    syl6d
    @52
    @28
    @25
    @19
    @14
    @28
    @25
    @19
    w3a
    @51
    @14
    @28
    @25
    @19
    @51
    @28
    @0
    @24
    wcel
    #
    @23
    wi
    #
    @0
    @7
    wcel
    #
    @18
    wi
    #
    wa
    #
    vk
    wal
    #
    @0
    cZ
    wcel
    #
    @50
    wi
    #
    vk
    wal
    @25
    @19
    wa
    #
    @51
    @28
    @69
    @72
    vk
    @28
    @71
    @65
    @67
    wo
    #
    @69
    @50
    @28
    @71
    @74
    @28
    @71
    wa
    #
    @74
    @4
    @0
    cuz
    cfv
    wcel
    #
    @67
    wo
    #
    @71
    @0
    cz
    wcel
    @4
    cz
    wcel
    @77
    @28
    cZ
    cz
    @0
    cZ
    @33
    cz
    cau3.1
    cM
    uzssz
    eqsstri
    #
    sseli
    cZ
    cz
    @4
    @78
    sseli
    @0
    @4
    uztric
    syl2anr
    @75
    @65
    @76
    @67
    @75
    @0
    @33
    wcel
    #
    @65
    @76
    wb
    @75
    @0
    cZ
    @33
    @28
    @71
    simpr
    cau3.1
    syl6eleq
    @65
    @79
    @76
    @0
    cM
    @4
    elfzuzb
    baib
    syl
    orbi1d
    mpbird
    ex
    @65
    @23
    @67
    @18
    pm3.48
    syl9
    alimdv
    @73
    @66
    vk
    wal
    #
    @68
    vk
    wal
    #
    wa
    @70
    @25
    @80
    @19
    @81
    @23
    vk
    @24
    df-ral
    @18
    vk
    @7
    df-ral
    anbi12i
    @66
    @68
    vk
    19.26
    bitr4i
    @50
    vk
    cZ
    df-ral
    3imtr4g
    3impib
    imim1i
    3expd
    syl6
    com23
    expimpd
    com3r
    com34
    rexlimdv
    mpd
    rexlimdvv
    sylsyld
    imp
end
