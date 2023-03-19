include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "chash.mm"
include "cfv.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cint.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "unifi.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "syl.mm"
include "simpl.mm"
include "pwfi.mm"
include "sylib.mm"
include "diffi.mm"
include "1cnd.mm"
include "negcld.mm"
include "cn.mm"
include "cn0.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "wb.mm"
include "eldifi.mm"
include "elpwi.mm"
include "ssfi.mm"
include "syl2an.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnm1nn0.mm"
include "expcld.mm"
include "simplr.mm"
include "sstrd.mm"
include "syl2anc.mm"
include "intssuni.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cin.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "0elpw.mm"
include "snssi.mm"
include "ax-mp.mm"
include "undif.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "adantr.mm"
include "inss1.mm"
include "sylancl.mm"
include "fsumsplit.mm"
include "inidm.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "subidd.mm"
include "syl5eq.mm"
include "incexclem.mm"
include "syldan.mm"
include "eqtr3d.mm"
include "negsubd.mm"
include "cvv.mm"
include "0ex.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "neg1cn.mm"
include "exp0.mm"
include "rint0.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "sumsn.mm"
include "sylancr.mm"
include "mulid2d.mm"
include "eqtr2d.mm"
include "fsumneg.mm"
include "expm1t.mm"
include "mulcomd.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "unissd.mm"
include "sseqin2.mm"
include "mulneg1d.mm"
include "sumeq2dv.mm"
include "3eqtr4rd.mm"
include "subeq0d.mm"

theorem incexc
  let cA: class A
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B

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
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
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
  assert |- ( ( A e. Fin /\ A C_ Fin ) -> ( # ` U. A ) = sum_ s e. ( ~P A \ { (/) } ) ( ( -u 1 ^ ( ( # ` s ) - 1 ) ) x. ( # ` |^| s ) ) )

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
    cA
    cpw
    #
    c0
    csn
    #
    cdif
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
    @9
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
    @2
    @3
    cfn
    wcel
    #
    @4
    cc
    wcel
    cA
    unifi
    #
    @17
    @4
    @3
    hashcl
    nn0cnd
    syl
    #
    @2
    @7
    @15
    vs
    @2
    @5
    cfn
    wcel
    #
    @7
    cfn
    wcel
    @2
    @0
    @20
    @0
    @1
    simpl
    #
    cA
    pwfi
    sylib
    #
    @5
    @6
    diffi
    syl
    #
    @2
    @9
    @7
    wcel
    #
    wa
    #
    @12
    @14
    @25
    @8
    @11
    @25
    c1
    @25
    1cnd
    negcld
    #
    @25
    @10
    cn
    wcel
    #
    @11
    cn0
    wcel
    @25
    @27
    @9
    c0
    wne
    #
    @24
    @28
    @2
    @9
    @5
    c0
    eldifsni
    adantl
    #
    @25
    @9
    cfn
    wcel
    #
    @27
    @28
    wb
    @2
    @0
    @9
    cA
    wss
    #
    @30
    @24
    @21
    @24
    @9
    @5
    wcel
    #
    @31
    @9
    @5
    @6
    eldifi
    @9
    cA
    elpwi
    #
    syl
    #
    cA
    @9
    ssfi
    #
    syl2an
    #
    @9
    hashnncl
    syl
    mpbird
    #
    @10
    nnm1nn0
    syl
    expcld
    #
    @25
    @14
    @25
    @13
    cfn
    wcel
    #
    @14
    cn0
    wcel
    @25
    @9
    cuni
    #
    cfn
    wcel
    #
    @13
    @40
    wss
    #
    @39
    @25
    @30
    @9
    cfn
    wss
    @41
    @36
    @25
    @9
    cA
    cfn
    @24
    @31
    @2
    @34
    adantl
    #
    @0
    @1
    @24
    simplr
    sstrd
    @9
    unifi
    syl2anc
    @25
    @28
    @42
    @29
    @9
    intssuni
    syl
    #
    @40
    @13
    ssfi
    syl2anc
    @13
    hashcl
    syl
    nn0cnd
    #
    mulcld
    #
    fsumcl
    #
    @2
    @5
    @8
    @10
    cexp
    co
    #
    @3
    @13
    cin
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
    @51
    vs
    csu
    #
    @7
    @51
    vs
    csu
    #
    caddc
    co
    #
    cc0
    @4
    @16
    cmin
    co
    #
    @2
    @6
    @7
    @51
    @5
    vs
    @6
    @7
    cin
    c0
    wceq
    @2
    @6
    @5
    disjdif
    a1i
    @5
    @6
    @7
    cun
    #
    wceq
    @2
    @57
    @5
    @6
    @5
    wss
    #
    @57
    @5
    wceq
    c0
    @5
    wcel
    @58
    cA
    0elpw
    c0
    @5
    snssi
    ax-mp
    @6
    @5
    undif
    mpbi
    eqcomi
    a1i
    @22
    @2
    @32
    wa
    #
    @48
    @50
    @59
    @8
    @10
    @59
    c1
    @59
    1cnd
    negcld
    @59
    @30
    @10
    cn0
    wcel
    @2
    @0
    @31
    @30
    @32
    @21
    @33
    @35
    syl2an
    @9
    hashcl
    syl
    expcld
    @59
    @50
    @59
    @49
    cfn
    wcel
    #
    @50
    cn0
    wcel
    @59
    @17
    @49
    @3
    wss
    @60
    @2
    @17
    @32
    @18
    adantr
    @3
    @13
    inss1
    @3
    @49
    ssfi
    sylancl
    @49
    hashcl
    syl
    nn0cnd
    mulcld
    fsumsplit
    @2
    @4
    @3
    @3
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    cc0
    @52
    @2
    @63
    @4
    @4
    cmin
    co
    cc0
    @62
    @4
    @4
    cmin
    @61
    @3
    chash
    @3
    inidm
    fveq2i
    oveq2i
    @2
    @4
    @19
    subidd
    syl5eq
    @0
    @1
    @17
    @63
    @52
    wceq
    @18
    cA
    @3
    vs
    incexclem
    syldan
    eqtr3d
    @2
    @4
    @16
    cneg
    #
    caddc
    co
    @56
    @55
    @2
    @4
    @16
    @19
    @47
    negsubd
    @2
    @4
    @53
    @64
    @54
    caddc
    @2
    @53
    c1
    @4
    cmul
    co
    #
    @4
    @2
    c0
    cvv
    wcel
    @65
    cc
    wcel
    @53
    @65
    wceq
    0ex
    @2
    c1
    @4
    @2
    1cnd
    @19
    mulcld
    @51
    @65
    vs
    c0
    cvv
    @9
    c0
    wceq
    #
    @48
    c1
    @50
    @4
    cmul
    @66
    @48
    @8
    cc0
    cexp
    co
    #
    c1
    @66
    @10
    cc0
    @8
    cexp
    @66
    @10
    c0
    chash
    cfv
    cc0
    @9
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq2d
    @8
    cc
    wcel
    #
    @67
    c1
    wceq
    neg1cn
    @8
    exp0
    ax-mp
    syl6eq
    @66
    @49
    @3
    chash
    @3
    @9
    rint0
    fveq2d
    oveq12d
    sumsn
    sylancr
    @2
    @4
    @19
    mulid2d
    eqtr2d
    @2
    @7
    @15
    cneg
    #
    vs
    csu
    @64
    @54
    @2
    @7
    @15
    vs
    @23
    @46
    fsumneg
    @2
    @7
    @69
    @51
    vs
    @25
    @51
    @12
    cneg
    #
    @14
    cmul
    co
    @69
    @25
    @48
    @70
    @50
    @14
    cmul
    @25
    @48
    @12
    @8
    cmul
    co
    #
    @8
    @12
    cmul
    co
    @70
    @25
    @68
    @27
    @48
    @71
    wceq
    @26
    @37
    @8
    @10
    expm1t
    syl2anc
    @25
    @12
    @8
    @38
    @26
    mulcomd
    @25
    @12
    @38
    mulm1d
    3eqtrd
    @25
    @49
    @13
    chash
    @25
    @13
    @3
    wss
    @49
    @13
    wceq
    @25
    @13
    @40
    @3
    @44
    @25
    @9
    cA
    @43
    unissd
    sstrd
    @13
    @3
    sseqin2
    sylib
    fveq2d
    oveq12d
    @25
    @12
    @14
    @38
    @45
    mulneg1d
    eqtr2d
    sumeq2dv
    eqtr3d
    oveq12d
    eqtr3d
    3eqtr4rd
    subeq0d
end
