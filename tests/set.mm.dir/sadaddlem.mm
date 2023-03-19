include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "cbits.mm"
include "cfv.mm"
include "csad.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cres.mm"
include "ccnv.mm"
include "fveq1i.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "fvres.mm"
include "syl.mm"
include "bitsmod.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cpw.mm"
include "cfn.mm"
include "wf1o.mm"
include "wi.mm"
include "bitsf1o.mm"
include "f1ocnvfv.mm"
include "sylancr.mm"
include "mpd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "moddifz.mm"
include "eqeltrd.mm"
include "wne.mm"
include "wb.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "wss.mm"
include "inss1.mm"
include "bitsss.mm"
include "sstri.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "elfpw.mm"
include "mpbir2an.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "feq1i.mm"
include "mpbir.mm"
include "ffvelrni.mm"
include "mp1i.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wa.mm"
include "dvds2add.mm"
include "mp2and.mm"
include "zcnd.mm"
include "nn0cnd.mm"
include "addsub4d.mm"
include "breqtrrd.mm"
include "zaddcld.mm"
include "moddvds.mm"
include "sadadd3.mm"
include "cle.mm"
include "clt.mm"
include "sadcl.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "fveq2i.mm"
include "f1ocnvfv2.mm"
include "3eqtr3a.mm"
include "syl6eqss.mm"
include "bitsfzo.mm"
include "elfzolt2.mm"
include "modid.mm"
include "syl22anc.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem sadaddlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  assume sadaddlem.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. ( bits ` A ) , m e. ( bits ` B ) , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadaddlem.k: |- K = `' ( bits |` NN0 )
  assume sadaddlem.1: |- ( ph -> A e. ZZ )
  assume sadaddlem.2: |- ( ph -> B e. ZZ )
  assume sadaddlem.3: |- ( ph -> N e. NN0 )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint N n
  disjoint c k
  disjoint k m
  disjoint k n
  disjoint A k
  disjoint B k
  assert |- ( ph -> ( ( ( bits ` A ) sadd ( bits ` B ) ) i^i ( 0 ..^ N ) ) = ( bits ` ( ( A + B ) mod ( 2 ^ N ) ) ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    c2
    cN
    cexp
    co
    #
    cmo
    co
    #
    cbits
    cfv
    cA
    cbits
    cfv
    #
    cB
    cbits
    cfv
    #
    csad
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    cbits
    cfv
    #
    @7
    wph
    @2
    @8
    cbits
    wph
    @2
    @3
    @6
    cin
    #
    cK
    cfv
    #
    @4
    @6
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    @1
    cmo
    co
    #
    @8
    @1
    cmo
    co
    #
    @8
    wph
    @2
    @15
    wceq
    #
    @1
    @0
    @14
    cmin
    co
    #
    cdvds
    wbr
    #
    wph
    @1
    cA
    @11
    cmin
    co
    #
    cB
    @13
    cmin
    co
    #
    caddc
    co
    #
    @18
    cdvds
    wph
    @1
    @20
    cdvds
    wbr
    #
    @1
    @21
    cdvds
    wbr
    #
    @1
    @22
    cdvds
    wbr
    #
    wph
    @23
    @20
    @1
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    @26
    cA
    cA
    @1
    cmo
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    cz
    wph
    @20
    @29
    @1
    cdiv
    wph
    @11
    @28
    cA
    cmin
    wph
    @11
    @10
    cbits
    cn0
    cres
    #
    ccnv
    #
    cfv
    #
    @28
    @10
    cK
    @32
    sadaddlem.k
    fveq1i
    wph
    @28
    @31
    cfv
    #
    @10
    wceq
    #
    @33
    @28
    wceq
    #
    wph
    @34
    @28
    cbits
    cfv
    #
    @10
    wph
    @28
    cn0
    wcel
    #
    @34
    @37
    wceq
    wph
    cA
    @1
    sadaddlem.1
    wph
    c2
    cN
    c2
    cn
    wcel
    wph
    2nn
    a1i
    sadaddlem.3
    nnexpcld
    #
    zmodcld
    #
    @28
    cn0
    cbits
    fvres
    syl
    wph
    cA
    cz
    wcel
    cN
    cn0
    wcel
    #
    @37
    @10
    wceq
    sadaddlem.1
    sadaddlem.3
    cN
    cA
    bitsmod
    syl2anc
    eqtrd
    wph
    cn0
    cn0
    cpw
    cfn
    cin
    #
    @31
    wf1o
    #
    @38
    @35
    @36
    wi
    bitsf1o
    @40
    cn0
    @42
    @28
    @10
    @31
    f1ocnvfv
    sylancr
    mpd
    syl5eq
    oveq2d
    oveq1d
    wph
    cA
    cr
    wcel
    @1
    crp
    wcel
    #
    @30
    cz
    wcel
    wph
    cA
    sadaddlem.1
    zred
    wph
    @1
    @39
    nnrpd
    #
    cA
    @1
    moddifz
    syl2anc
    eqeltrd
    wph
    @1
    cz
    wcel
    #
    @1
    cc0
    wne
    #
    @20
    cz
    wcel
    #
    @23
    @27
    wb
    wph
    @1
    @39
    nnzd
    #
    wph
    @1
    @39
    nnne0d
    #
    wph
    cA
    @11
    sadaddlem.1
    wph
    @11
    @10
    @42
    wcel
    #
    @11
    cn0
    wcel
    wph
    @51
    @10
    cn0
    wss
    @10
    cfn
    wcel
    #
    @10
    @3
    cn0
    @3
    @6
    inss1
    cA
    bitsss
    #
    sstri
    @6
    cfn
    wcel
    #
    @10
    @6
    wss
    @52
    cc0
    cN
    fzofi
    #
    @3
    @6
    inss2
    @6
    @10
    ssfi
    mp2an
    @10
    cn0
    elfpw
    mpbir2an
    @42
    cn0
    @10
    cK
    @42
    cn0
    cK
    wf
    @42
    cn0
    @32
    wf
    #
    @43
    @42
    cn0
    @32
    wf1o
    @56
    bitsf1o
    cn0
    @42
    @31
    f1ocnv
    @42
    cn0
    @32
    f1of
    mp2b
    @42
    cn0
    cK
    @32
    sadaddlem.k
    feq1i
    mpbir
    #
    ffvelrni
    mp1i
    #
    nn0zd
    #
    zsubcld
    #
    @1
    @20
    dvdsval2
    syl3anc
    mpbird
    wph
    @24
    @21
    @1
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    @61
    cB
    cB
    @1
    cmo
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    cz
    wph
    @21
    @64
    @1
    cdiv
    wph
    @13
    @63
    cB
    cmin
    wph
    @13
    @12
    @32
    cfv
    #
    @63
    @12
    cK
    @32
    sadaddlem.k
    fveq1i
    wph
    @63
    @31
    cfv
    #
    @12
    wceq
    #
    @66
    @63
    wceq
    #
    wph
    @67
    @63
    cbits
    cfv
    #
    @12
    wph
    @63
    cn0
    wcel
    #
    @67
    @70
    wceq
    wph
    cB
    @1
    sadaddlem.2
    @39
    zmodcld
    #
    @63
    cn0
    cbits
    fvres
    syl
    wph
    cB
    cz
    wcel
    @41
    @70
    @12
    wceq
    sadaddlem.2
    sadaddlem.3
    cN
    cB
    bitsmod
    syl2anc
    eqtrd
    wph
    @43
    @71
    @68
    @69
    wi
    bitsf1o
    @72
    cn0
    @42
    @63
    @12
    @31
    f1ocnvfv
    sylancr
    mpd
    syl5eq
    oveq2d
    oveq1d
    wph
    cB
    cr
    wcel
    @44
    @65
    cz
    wcel
    wph
    cB
    sadaddlem.2
    zred
    @45
    cB
    @1
    moddifz
    syl2anc
    eqeltrd
    wph
    @46
    @47
    @21
    cz
    wcel
    #
    @24
    @62
    wb
    @49
    @50
    wph
    cB
    @13
    sadaddlem.2
    wph
    @13
    @12
    @42
    wcel
    #
    @13
    cn0
    wcel
    wph
    @74
    @12
    cn0
    wss
    @12
    cfn
    wcel
    #
    @12
    @4
    cn0
    @4
    @6
    inss1
    cB
    bitsss
    #
    sstri
    @54
    @12
    @6
    wss
    @75
    @55
    @4
    @6
    inss2
    @6
    @12
    ssfi
    mp2an
    @12
    cn0
    elfpw
    mpbir2an
    @42
    cn0
    @12
    cK
    @57
    ffvelrni
    mp1i
    #
    nn0zd
    #
    zsubcld
    #
    @1
    @21
    dvdsval2
    syl3anc
    mpbird
    wph
    @46
    @48
    @73
    @23
    @24
    wa
    @25
    wi
    @49
    @60
    @79
    @1
    @20
    @21
    dvds2add
    syl3anc
    mp2and
    wph
    cA
    cB
    @11
    @13
    wph
    cA
    sadaddlem.1
    zcnd
    wph
    cB
    sadaddlem.2
    zcnd
    wph
    @11
    @58
    nn0cnd
    wph
    @13
    @77
    nn0cnd
    addsub4d
    breqtrrd
    wph
    @1
    cn
    wcel
    @0
    cz
    wcel
    @14
    cz
    wcel
    @17
    @19
    wb
    @39
    wph
    cA
    cB
    sadaddlem.1
    sadaddlem.2
    zaddcld
    wph
    @11
    @13
    @59
    @78
    zaddcld
    @0
    @14
    @1
    moddvds
    syl3anc
    mpbird
    wph
    @3
    @4
    cC
    vm
    vn
    cK
    cN
    vc
    @3
    cn0
    wss
    #
    wph
    @53
    a1i
    @4
    cn0
    wss
    #
    wph
    @76
    a1i
    sadaddlem.c
    sadaddlem.3
    sadaddlem.k
    sadadd3
    wph
    @8
    cr
    wcel
    @44
    cc0
    @8
    cle
    wbr
    @8
    @1
    clt
    wbr
    #
    @16
    @8
    wceq
    wph
    @8
    @7
    @42
    wcel
    #
    @8
    cn0
    wcel
    #
    wph
    @83
    @7
    cn0
    wss
    @7
    cfn
    wcel
    #
    @7
    @5
    cn0
    @5
    @6
    inss1
    @80
    @81
    @5
    cn0
    wss
    @53
    @76
    @3
    @4
    sadcl
    mp2an
    sstri
    @54
    @7
    @6
    wss
    @85
    @55
    @5
    @6
    inss2
    #
    @6
    @7
    ssfi
    mp2an
    @7
    cn0
    elfpw
    mpbir2an
    #
    @42
    cn0
    @7
    cK
    @57
    ffvelrni
    mp1i
    #
    nn0red
    @45
    wph
    @8
    @88
    nn0ge0d
    wph
    @8
    cc0
    @1
    cfzo
    co
    wcel
    #
    @82
    wph
    @89
    @9
    @6
    wss
    #
    wph
    @9
    @7
    @6
    wph
    @8
    @31
    cfv
    #
    @7
    @32
    cfv
    #
    @31
    cfv
    #
    @9
    @7
    @8
    @92
    @31
    @7
    cK
    @32
    sadaddlem.k
    fveq1i
    fveq2i
    wph
    @84
    @91
    @9
    wceq
    @88
    @8
    cn0
    cbits
    fvres
    syl
    wph
    @43
    @83
    @93
    @7
    wceq
    bitsf1o
    @83
    wph
    @87
    a1i
    cn0
    @42
    @7
    @31
    f1ocnvfv2
    sylancr
    3eqtr3a
    #
    @86
    syl6eqss
    wph
    @8
    cz
    wcel
    @41
    @89
    @90
    wb
    wph
    @8
    @88
    nn0zd
    sadaddlem.3
    cN
    @8
    bitsfzo
    syl2anc
    mpbird
    @8
    cc0
    @1
    elfzolt2
    syl
    @8
    @1
    modid
    syl22anc
    3eqtr2d
    fveq2d
    @94
    eqtr2d
end
