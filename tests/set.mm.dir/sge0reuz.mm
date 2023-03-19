include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cfz.mm"
include "co.mm"
include "cvv.mm"
include "cuz.mm"
include "wceq.mm"
include "a1i.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "sge0revalmpt.mm"
include "wss.mm"
include "wcel.mm"
include "nfv.mm"
include "eqid.mm"
include "wa.mm"
include "nfan.mm"
include "elinel2.mm"
include "adantl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "simpll.mm"
include "elpwinss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "fsumreclf.mm"
include "rexrd.mm"
include "rnmptssd.mm"
include "supxrcl.mm"
include "syl.mm"
include "fzfid.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syldan.mm"
include "adantlr.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "w3a.mm"
include "cz.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3adant3.mm"
include "uzfissfz.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfrex.mm"
include "wi.mm"
include "id.mm"
include "sumex.mm"
include "elrnmpt1.mm"
include "simplr.mm"
include "nfcv.mm"
include "nfsum1.mm"
include "nfeq.mm"
include "ad4ant14.mm"
include "simplll.mm"
include "0xr.mm"
include "pnfxr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "fsumlessf.mm"
include "eqbrtrd.mm"
include "3adant2.mm"
include "breq2.mm"
include "rspcev.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "imp.mm"
include "suplesup2.mm"
include "wral.mm"
include "ssriv.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbir.mm"
include "fzfi.mm"
include "elini.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "elrnmptd.mm"
include "2a1i.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "supxrss.mm"
include "xrletrid.mm"
include "eqtrd.mm"

theorem sge0reuz
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cZ: class Z
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume sge0reuz.k: |- F/ k ph
  assume sge0reuz.m: |- ( ph -> M e. ZZ )
  assume sge0reuz.z: |- Z = ( ZZ>= ` M )
  assume sge0reuz.b: |- ( ( ph /\ k e. Z ) -> B e. ( 0 [,) +oo ) )

  disjoint B n
  disjoint M k
  disjoint M n
  disjoint k n
  disjoint Z k
  disjoint Z n
  disjoint n ph
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. Z |-> B ) ) = sup ( ran ( n e. Z |-> sum_ k e. ( M ... n ) B ) , RR* , < ) )

  proof
    wph
    vk
    cZ
    cB
    cmpt
    csumge0
    cfv
    vx
    cZ
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    cB
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    vn
    cZ
    cM
    vn
    cv
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    wph
    vk
    vx
    cZ
    cB
    cvv
    sge0reuz.k
    wph
    cZ
    cM
    cuz
    cfv
    #
    cvv
    cZ
    @13
    wceq
    wph
    sge0reuz.z
    a1i
    cM
    cuz
    fvex
    syl6eqel
    sge0reuz.b
    sge0revalmpt
    wph
    @6
    @12
    wph
    @5
    cxr
    wss
    #
    @6
    cxr
    wcel
    wph
    vx
    @1
    @3
    cxr
    @4
    wph
    vx
    nfv
    @4
    eqid
    #
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @17
    @2
    cB
    vk
    wph
    @16
    vk
    sge0reuz.k
    @16
    vk
    nfv
    nfan
    @16
    @2
    cfn
    wcel
    #
    wph
    @2
    @0
    cfn
    elinel2
    adantl
    #
    @17
    vk
    cv
    #
    @2
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    cB
    rge0ssre
    @22
    wph
    @20
    cZ
    wcel
    #
    cB
    @23
    wcel
    #
    wph
    @16
    @21
    simpll
    @16
    @21
    @24
    wph
    @16
    @21
    wa
    @2
    cZ
    @20
    @16
    @2
    cZ
    wss
    #
    @21
    @2
    cZ
    cfn
    elpwinss
    #
    adantr
    @16
    @21
    simpr
    sseldd
    adantll
    sge0reuz.b
    syl2anc
    sseldi
    fsumreclf
    rexrd
    rnmptssd
    #
    @5
    supxrcl
    syl
    wph
    @11
    cxr
    wss
    @12
    cxr
    wcel
    wph
    vn
    cZ
    @9
    cxr
    @10
    wph
    vn
    nfv
    @10
    eqid
    #
    wph
    @7
    cZ
    wcel
    #
    wa
    #
    @9
    @31
    @8
    cB
    vk
    wph
    @30
    vk
    sge0reuz.k
    @30
    vk
    nfv
    nfan
    @31
    cM
    @7
    fzfid
    wph
    @20
    @8
    wcel
    #
    cB
    cr
    wcel
    #
    @30
    wph
    @32
    @24
    @33
    @32
    @24
    wph
    @32
    @20
    @13
    cZ
    @20
    cM
    @7
    elfzuz
    sge0reuz.z
    syl6eleqr
    #
    adantl
    wph
    @24
    wa
    #
    @23
    cr
    cB
    rge0ssre
    sge0reuz.b
    sseldi
    syldan
    #
    adantlr
    fsumreclf
    rexrd
    rnmptssd
    #
    @11
    supxrcl
    syl
    wph
    vy
    vw
    @5
    @11
    @28
    @37
    wph
    vy
    cv
    #
    @5
    wcel
    #
    @38
    @3
    wceq
    #
    vx
    @1
    wrex
    #
    @38
    vw
    cv
    #
    cle
    wbr
    #
    vw
    @11
    wrex
    #
    @39
    @41
    wph
    @39
    @41
    @38
    cvv
    wcel
    #
    @39
    @41
    wb
    vy
    vex
    #
    vx
    @1
    @3
    @38
    @4
    cvv
    @15
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @41
    @44
    wph
    @40
    @44
    vx
    @1
    wph
    @16
    @40
    @44
    wph
    @16
    @40
    w3a
    #
    @2
    @8
    wss
    #
    vn
    cZ
    wrex
    @44
    @47
    @2
    vn
    cM
    cZ
    wph
    @16
    cM
    cz
    wcel
    @40
    sge0reuz.m
    3ad2ant1
    sge0reuz.z
    @16
    wph
    @26
    @40
    @27
    3ad2ant2
    wph
    @16
    @18
    @40
    @19
    3adant3
    uzfissfz
    @47
    @48
    @44
    vn
    cZ
    @47
    vn
    nfv
    @43
    vn
    vw
    @11
    vn
    @10
    vn
    cZ
    @9
    nfmpt1
    nfrn
    @43
    vn
    nfv
    nfrex
    wph
    @40
    @30
    @48
    @44
    wi
    wi
    @16
    wph
    @40
    wa
    #
    @30
    @48
    @44
    @49
    @30
    @48
    w3a
    @9
    @11
    wcel
    #
    @38
    @9
    cle
    wbr
    #
    @44
    @30
    @49
    @50
    @48
    @30
    @30
    @9
    cvv
    wcel
    #
    @50
    @30
    id
    @52
    @30
    @8
    cB
    vk
    sumex
    a1i
    vn
    cZ
    @9
    @10
    cvv
    @29
    elrnmpt1
    syl2anc
    3ad2ant2
    @49
    @48
    @51
    @30
    @49
    @48
    wa
    #
    @38
    @3
    @9
    cle
    wph
    @40
    @48
    simplr
    @53
    @8
    cB
    @2
    vk
    @49
    @48
    vk
    wph
    @40
    vk
    sge0reuz.k
    vk
    @38
    @3
    vk
    @38
    nfcv
    @2
    cB
    vk
    vk
    @2
    nfcv
    nfsum1
    nfeq
    nfan
    @48
    vk
    nfv
    nfan
    @53
    cM
    @7
    fzfid
    wph
    @32
    @33
    @40
    @48
    @36
    ad4ant14
    @53
    @32
    wa
    wph
    @24
    cc0
    cB
    cle
    wbr
    #
    wph
    @40
    @48
    @32
    simplll
    @32
    @24
    @53
    @34
    adantl
    @35
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @25
    @54
    @55
    @35
    0xr
    a1i
    @56
    @35
    pnfxr
    a1i
    sge0reuz.b
    cc0
    cpnf
    cB
    icogelb
    syl3anc
    syl2anc
    @49
    @48
    simpr
    fsumlessf
    eqbrtrd
    3adant2
    @43
    @51
    vw
    @9
    @11
    @42
    @9
    @38
    cle
    breq2
    rspcev
    syl2anc
    3exp
    3adant2
    rexlimd
    mpd
    3exp
    rexlimdv
    imp
    syldan
    suplesup2
    wph
    @11
    @5
    wss
    #
    @14
    @12
    @6
    cle
    wbr
    wph
    @39
    vy
    @11
    wral
    @57
    wph
    @39
    vy
    @11
    wph
    @38
    @11
    wcel
    #
    wa
    @38
    @9
    wceq
    #
    vn
    cZ
    wrex
    #
    @39
    @58
    @60
    wph
    @58
    @60
    @45
    @58
    @60
    wb
    @46
    vn
    cZ
    @9
    @38
    @10
    cvv
    @29
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @60
    @39
    wi
    @58
    wph
    @59
    @39
    vn
    cZ
    @59
    @39
    wi
    wph
    @30
    @59
    vx
    @1
    @3
    @38
    @4
    cvv
    @15
    @59
    @8
    @1
    wcel
    #
    @59
    @41
    @61
    @59
    @8
    @0
    cfn
    @8
    @0
    wcel
    @8
    cZ
    wss
    vk
    @8
    cZ
    @34
    ssriv
    @8
    cZ
    cM
    @7
    cfz
    ovex
    elpw
    mpbir
    cM
    @7
    fzfi
    elini
    a1i
    @59
    id
    @40
    @59
    vx
    @8
    @1
    @2
    @8
    wceq
    @3
    @9
    @38
    @2
    @8
    cB
    vk
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    @45
    @59
    @46
    a1i
    elrnmptd
    2a1i
    rexlimdv
    adantr
    mpd
    ralrimiva
    vy
    @11
    @5
    dfss3
    sylibr
    @28
    @11
    @5
    supxrss
    syl2anc
    xrletrid
    eqtrd
end
