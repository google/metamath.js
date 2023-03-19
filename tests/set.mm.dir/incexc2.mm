include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "ciun.mm"
include "cneg.mm"
include "cmin.mm"
include "cexp.mm"
include "cint.mm"
include "cmul.mm"
include "csu.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "incexc.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "cn.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "cn0.mm"
include "hashcl.mm"
include "ad2antrr.mm"
include "nn0zd.mm"
include "cdom.mm"
include "simpl.mm"
include "elpwi.mm"
include "ssdomg.mm"
include "imp.mm"
include "syl2an.mm"
include "hashdomi.mm"
include "syl.mm"
include "fznn.mm"
include "rbaibd.mm"
include "syl2anc.mm"
include "ssfi.mm"
include "hashnncl.mm"
include "bitr2d.mm"
include "df-ne.mm"
include "risset.mm"
include "3bitr3g.mm"
include "velsn.mm"
include "notbii.mm"
include "eqcom.mm"
include "rexbii.mm"
include "3bitr4g.mm"
include "rabbidva.mm"
include "dfdif2.mm"
include "iunrab.mm"
include "3eqtr4g.mm"
include "sumeq1d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "simpll.mm"
include "pwfi.mm"
include "sylib.mm"
include "ssrab2.mm"
include "sylancl.mm"
include "wral.mm"
include "wdisj.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "invdisj.mm"
include "cc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "1cnd.mm"
include "negcld.mm"
include "elfznn.mm"
include "nnm1nn0.mm"
include "expcld.mm"
include "adantr.mm"
include "unifi.mm"
include "eqeltrd.mm"
include "elrabi.mm"
include "mpbid.mm"
include "intssuni.mm"
include "unissd.mm"
include "sstrd.mm"
include "nn0cnd.mm"
include "mulcld.mm"
include "anasss.mm"
include "fsumiun.mm"
include "sumeq2dv.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem incexc2
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint k n
  disjoint k s
  disjoint A k
  disjoint n s
  disjoint A n
  disjoint A s
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n t
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B b
  disjoint B s
  assert |- ( ( A e. Fin /\ A C_ Fin ) -> ( # ` U. A ) = sum_ n e. ( 1 ... ( # ` A ) ) ( ( -u 1 ^ ( n - 1 ) ) x. sum_ s e. { k e. ~P A | ( # ` k ) = n } ( # ` |^| s ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cfn
    wss
    #
    wa
    #
    cA
    cuni
    #
    chash
    cfv
    #
    vn
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    chash
    cfv
    #
    vn
    cv
    #
    wceq
    #
    vk
    cA
    cpw
    #
    crab
    #
    ciun
    #
    c1
    cneg
    #
    vs
    cv
    #
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    @15
    cint
    #
    chash
    cfv
    #
    cmul
    co
    #
    vs
    csu
    #
    @6
    @12
    @21
    vs
    csu
    #
    vn
    csu
    @6
    @14
    @9
    c1
    cmin
    co
    #
    cexp
    co
    #
    @12
    @20
    vs
    csu
    cmul
    co
    #
    vn
    csu
    @2
    @4
    @11
    c0
    csn
    #
    cdif
    #
    @21
    vs
    csu
    @22
    cA
    vs
    incexc
    @2
    @28
    @13
    @21
    vs
    @2
    @7
    @27
    wcel
    #
    wn
    #
    vk
    @11
    crab
    @10
    vn
    @6
    wrex
    #
    vk
    @11
    crab
    @28
    @13
    @2
    @30
    @31
    vk
    @11
    @2
    @7
    @11
    wcel
    #
    wa
    #
    @7
    c0
    wceq
    #
    wn
    #
    @9
    @8
    wceq
    #
    vn
    @6
    wrex
    #
    @30
    @31
    @33
    @7
    c0
    wne
    #
    @8
    @6
    wcel
    #
    @35
    @37
    @33
    @39
    @8
    cn
    wcel
    #
    @38
    @33
    @5
    cz
    wcel
    #
    @8
    @5
    cle
    wbr
    #
    @39
    @40
    wb
    @33
    @5
    @0
    @5
    cn0
    wcel
    @1
    @32
    cA
    hashcl
    ad2antrr
    nn0zd
    @33
    @7
    cA
    cdom
    wbr
    #
    @42
    @2
    @0
    @7
    cA
    wss
    #
    @43
    @32
    @0
    @1
    simpl
    #
    @7
    cA
    elpwi
    #
    @0
    @44
    @43
    @7
    cA
    cfn
    ssdomg
    imp
    syl2an
    @7
    cA
    hashdomi
    syl
    @41
    @39
    @40
    @42
    @8
    @5
    fznn
    rbaibd
    syl2anc
    @33
    @7
    cfn
    wcel
    #
    @40
    @38
    wb
    @2
    @0
    @44
    @47
    @32
    @45
    @46
    cA
    @7
    ssfi
    syl2an
    @7
    hashnncl
    syl
    bitr2d
    @7
    c0
    df-ne
    vn
    @8
    @6
    risset
    3bitr3g
    @29
    @34
    vk
    c0
    velsn
    notbii
    @10
    @36
    vn
    @6
    @8
    @9
    eqcom
    rexbii
    3bitr4g
    rabbidva
    vk
    @11
    @27
    dfdif2
    @10
    vn
    vk
    @6
    @11
    iunrab
    3eqtr4g
    sumeq1d
    eqtrd
    @2
    vn
    @6
    @12
    @21
    vs
    @2
    c1
    @5
    fzfid
    @2
    @9
    @6
    wcel
    #
    wa
    #
    @11
    cfn
    wcel
    #
    @12
    @11
    wss
    @12
    cfn
    wcel
    @49
    @0
    @50
    @0
    @1
    @48
    simpll
    #
    cA
    pwfi
    sylib
    @10
    vk
    @11
    ssrab2
    @11
    @12
    ssfi
    sylancl
    #
    @2
    @16
    @9
    wceq
    #
    vs
    @12
    wral
    #
    vn
    @6
    wral
    vn
    @6
    @12
    wdisj
    @2
    @54
    vn
    @6
    @49
    @53
    vs
    @12
    @15
    @12
    wcel
    #
    @53
    @49
    @55
    @15
    @11
    wcel
    #
    @53
    @10
    @53
    vk
    @15
    @11
    @7
    @15
    wceq
    @8
    @16
    @9
    @7
    @15
    chash
    fveq2
    eqeq1d
    elrab
    simprbi
    adantl
    #
    ralrimiva
    ralrimiva
    vn
    vs
    @6
    @12
    @16
    invdisj
    syl
    @2
    @48
    @55
    @21
    cc
    wcel
    @49
    @55
    wa
    #
    @21
    @25
    @20
    cmul
    co
    #
    cc
    @58
    @18
    @25
    @20
    cmul
    @58
    @17
    @24
    @14
    cexp
    @58
    @16
    @9
    c1
    cmin
    @57
    oveq1d
    oveq2d
    oveq1d
    #
    @58
    @25
    @20
    @49
    @25
    cc
    wcel
    @55
    @49
    @14
    @24
    @49
    c1
    @49
    1cnd
    negcld
    @49
    @9
    cn
    wcel
    #
    @24
    cn0
    wcel
    @48
    @61
    @2
    @9
    @5
    elfznn
    adantl
    #
    @9
    nnm1nn0
    syl
    expcld
    #
    adantr
    @58
    @20
    @58
    @19
    cfn
    wcel
    #
    @20
    cn0
    wcel
    @58
    @3
    cfn
    wcel
    #
    @19
    @3
    wss
    @64
    @2
    @65
    @48
    @55
    cA
    unifi
    ad2antrr
    @58
    @19
    @15
    cuni
    #
    @3
    @58
    @15
    c0
    wne
    #
    @19
    @66
    wss
    @58
    @16
    cn
    wcel
    #
    @67
    @58
    @16
    @9
    cn
    @57
    @49
    @61
    @55
    @62
    adantr
    eqeltrd
    @58
    @15
    cfn
    wcel
    #
    @68
    @67
    wb
    @58
    @0
    @15
    cA
    wss
    #
    @69
    @49
    @0
    @55
    @51
    adantr
    @58
    @56
    @70
    @55
    @56
    @49
    @10
    vk
    @15
    @11
    elrabi
    adantl
    @15
    cA
    elpwi
    syl
    #
    cA
    @15
    ssfi
    syl2anc
    @15
    hashnncl
    syl
    mpbid
    @15
    intssuni
    syl
    @58
    @15
    cA
    @71
    unissd
    sstrd
    @3
    @19
    ssfi
    syl2anc
    @19
    hashcl
    syl
    nn0cnd
    #
    mulcld
    eqeltrd
    anasss
    fsumiun
    @2
    @6
    @23
    @26
    vn
    @49
    @23
    @12
    @59
    vs
    csu
    @26
    @49
    @12
    @21
    @59
    vs
    @60
    sumeq2dv
    @49
    @12
    @20
    @25
    vs
    @52
    @63
    @72
    fsummulc2
    eqtr4d
    sumeq2dv
    3eqtrd
end
