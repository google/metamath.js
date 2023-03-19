include "cv.mm"
include "clgam.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "caddc.mm"
include "cof.mm"
include "c1.mm"
include "cseq.mm"
include "clog.mm"
include "co.mm"
include "cmpt.mm"
include "culm.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "csu.mm"
include "cz.mm"
include "cdif.mm"
include "cvv.mm"
include "wceq.mm"
include "lgamgulmlem1.mm"
include "sselda.mm"
include "ovex.mm"
include "df-lgam.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "nnuz.mm"
include "1zzd.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eldifad.mm"
include "adantr.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "dmgmdivn0.mm"
include "logcld.mm"
include "subcld.mm"
include "cmap.mm"
include "wf.mm"
include "wfn.mm"
include "cuz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "cdm.mm"
include "lgamgulm.mm"
include "ulmdm.mm"
include "sylib.mm"
include "ulmf2.mm"
include "sylancr.mm"
include "seqex.mm"
include "a1i.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "cabs.mm"
include "cle.mm"
include "cn0.mm"
include "cnex.mm"
include "rabex2.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "ovexd.mm"
include "seqof2.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "fvex.mm"
include "ulmclm.mm"
include "isumclim.mm"
include "ulmcl.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "dmgmn0.mm"
include "ralrimiva.mm"
include "ffn.mm"
include "3syl.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nfseq.mm"
include "nffv.mm"
include "dffn5f.mm"
include "npcand.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "breqtrd.mm"
include "jca.mm"

theorem lgamgulm2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vt: setvar t
  let cN: class N
  let cA: class A
  let cO: class O
  let cT: class T
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )

  disjoint k m
  disjoint k x
  disjoint k z
  disjoint R k
  disjoint m x
  disjoint m z
  disjoint R m
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint U m
  disjoint U z
  disjoint m ph
  disjoint ph x
  disjoint ph z
  disjoint n r
  disjoint n y
  disjoint G n
  disjoint r y
  disjoint G r
  disjoint G y
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m y
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint t z
  disjoint R t
  disjoint y z
  disjoint R y
  disjoint U n
  disjoint U r
  disjoint U t
  disjoint U y
  disjoint A k
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph y
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> ( A. z e. U ( log_G ` z ) e. CC /\ seq 1 ( oF + , G ) ( ~~>u ` U ) ( z e. U |-> ( ( log_G ` z ) + ( log ` z ) ) ) ) )

  proof
    wph
    vz
    cv
    #
    clgam
    cfv
    #
    cc
    wcel
    #
    vz
    cU
    wral
    caddc
    cof
    #
    cG
    c1
    cseq
    #
    vz
    cU
    @1
    @0
    clog
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cU
    culm
    cfv
    #
    wbr
    wph
    @2
    vz
    cU
    wph
    @0
    cU
    wcel
    #
    wa
    #
    @1
    cn
    @0
    vn
    cv
    #
    c1
    caddc
    co
    #
    @11
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @0
    @11
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    vn
    csu
    #
    @5
    cmin
    co
    #
    cc
    @10
    @0
    cc
    cz
    cn
    cdif
    #
    cdif
    #
    wcel
    #
    @21
    cvv
    wcel
    @1
    @21
    wceq
    wph
    cU
    @23
    @0
    wph
    vx
    cR
    cU
    vk
    lgamgulm.r
    lgamgulm.u
    lgamgulmlem1
    sselda
    #
    @20
    @5
    cmin
    ovex
    vz
    @23
    @21
    cvv
    clgam
    vz
    vn
    df-lgam
    fvmpt2
    sylancl
    #
    @10
    @20
    @5
    @10
    @20
    @0
    @4
    @8
    cfv
    #
    cfv
    #
    cc
    @10
    @19
    @28
    vn
    vm
    cn
    @0
    vm
    cv
    #
    c1
    caddc
    co
    #
    @29
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @0
    @29
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    @10
    1zzd
    #
    @11
    cn
    wcel
    #
    @11
    @38
    cfv
    @19
    wceq
    @10
    vm
    @11
    @37
    @19
    cn
    @38
    @29
    @11
    wceq
    #
    @33
    @15
    @36
    @18
    cmin
    @41
    @32
    @14
    @0
    cmul
    @41
    @31
    @13
    clog
    @41
    @30
    @12
    @29
    @11
    cdiv
    @29
    @11
    c1
    caddc
    oveq1
    @41
    id
    oveq12d
    fveq2d
    oveq2d
    @41
    @35
    @17
    clog
    @41
    @34
    @16
    c1
    caddc
    @29
    @11
    @0
    cdiv
    oveq2
    oveq1d
    fveq2d
    oveq12d
    @38
    eqid
    @15
    @18
    cmin
    ovex
    fvmpt
    adantl
    @10
    @40
    wa
    #
    @15
    @18
    @42
    @0
    @14
    @10
    @0
    cc
    wcel
    @40
    @10
    @0
    cc
    @22
    @25
    eldifad
    #
    adantr
    #
    @42
    @14
    @42
    @13
    @42
    @12
    @11
    @42
    @12
    @42
    @11
    @10
    @40
    simpr
    #
    peano2nnd
    nnrpd
    @42
    @11
    @45
    nnrpd
    rpdivcld
    relogcld
    recnd
    mulcld
    @42
    @17
    @42
    @16
    c1
    @42
    @0
    @11
    @44
    @42
    @11
    @45
    nncnd
    @42
    @11
    @45
    nnne0d
    divcld
    @42
    1cnd
    addcld
    @42
    @0
    @11
    @10
    @24
    @40
    @25
    adantr
    @45
    dmgmdivn0
    logcld
    subcld
    @10
    @0
    cU
    vn
    @4
    @27
    caddc
    @38
    c1
    cseq
    #
    c1
    cvv
    cn
    nnuz
    @39
    wph
    cn
    cc
    cU
    cmap
    co
    @4
    wf
    #
    @9
    wph
    @4
    cn
    wfn
    #
    @4
    @27
    @8
    wbr
    #
    @47
    @48
    @4
    c1
    cuz
    cfv
    #
    wfn
    #
    c1
    cz
    wcel
    @51
    1z
    @3
    cG
    c1
    seqfn
    ax-mp
    cn
    @50
    @4
    nnuz
    fneq2i
    mpbir
    wph
    @4
    @8
    cdm
    wcel
    @49
    wph
    vx
    vz
    cR
    cU
    vk
    vm
    cG
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    lgamgulm
    cU
    @4
    ulmdm
    sylib
    #
    cU
    @4
    @27
    cn
    ulmf2
    sylancr
    adantr
    wph
    @9
    simpr
    #
    @46
    cvv
    wcel
    @10
    caddc
    @38
    c1
    seqex
    a1i
    @42
    @0
    @11
    @4
    cfv
    #
    cfv
    @0
    vz
    cU
    @11
    @46
    cfv
    #
    cmpt
    #
    cfv
    #
    @55
    @42
    @0
    @54
    @56
    @42
    @54
    @11
    @3
    vm
    cn
    vz
    cU
    @37
    cmpt
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    @56
    @42
    @11
    @4
    @60
    @42
    cG
    @59
    @3
    c1
    cG
    @59
    wceq
    @42
    lgamgulm.g
    a1i
    seqeq3d
    fveq1d
    wph
    @40
    @61
    @56
    wceq
    @9
    wph
    @40
    wa
    #
    vm
    vz
    cU
    cn
    caddc
    c1
    @11
    cvv
    cvv
    @37
    cU
    cvv
    wcel
    @62
    vx
    cv
    #
    cabs
    cfv
    cR
    cle
    wbr
    c1
    cR
    cdiv
    co
    @63
    vk
    cv
    caddc
    co
    cabs
    cfv
    cle
    wbr
    vk
    cn0
    wral
    wa
    vx
    cc
    cU
    lgamgulm.u
    cnex
    rabex2
    a1i
    @62
    @11
    cn
    @50
    wph
    @40
    simpr
    nnuz
    syl6eleq
    c1
    @11
    cfz
    co
    cn
    wss
    @62
    @11
    fz1ssnn
    a1i
    @62
    @29
    cn
    wcel
    @9
    wa
    wa
    @33
    @36
    cmin
    ovexd
    seqof2
    adantlr
    eqtrd
    fveq1d
    @42
    @9
    @55
    cvv
    wcel
    @57
    @55
    wceq
    @10
    @9
    @40
    @53
    adantr
    @11
    @46
    fvex
    vz
    cU
    @55
    cvv
    @56
    @56
    eqid
    fvmpt2
    sylancl
    eqtrd
    wph
    @49
    @9
    @52
    adantr
    ulmclm
    isumclim
    #
    wph
    cU
    cc
    @0
    @27
    wph
    @49
    cU
    cc
    @27
    wf
    #
    @52
    cU
    @4
    @27
    ulmcl
    #
    syl
    ffvelrnda
    eqeltrd
    #
    @10
    @0
    @43
    @10
    @0
    @25
    dmgmn0
    logcld
    #
    subcld
    eqeltrd
    ralrimiva
    wph
    @4
    @27
    @7
    @8
    @52
    wph
    @27
    vz
    cU
    @28
    cmpt
    #
    @7
    wph
    @27
    cU
    wfn
    #
    @27
    @69
    wceq
    wph
    @49
    @65
    @70
    @52
    @66
    cU
    cc
    @27
    ffn
    3syl
    vz
    cU
    @27
    vz
    @4
    @8
    vz
    @8
    nfcv
    vz
    @3
    cG
    c1
    vz
    c1
    nfcv
    vz
    @3
    nfcv
    vz
    cG
    @59
    lgamgulm.g
    vz
    vm
    cn
    @58
    vz
    cn
    nfcv
    vz
    cU
    @37
    nfmpt1
    nfmpt
    nfcxfr
    nfseq
    nffv
    dffn5f
    sylib
    wph
    vz
    cU
    @28
    @6
    @10
    @6
    @21
    @5
    caddc
    co
    @20
    @28
    @10
    @1
    @21
    @5
    caddc
    @26
    oveq1d
    @10
    @20
    @5
    @67
    @68
    npcand
    @64
    3eqtrrd
    mpteq2dva
    eqtrd
    breqtrd
    jca
end
