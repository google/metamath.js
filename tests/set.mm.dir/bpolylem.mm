include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cbp.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "cpred.mm"
include "cres.mm"
include "cexp.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cvv.mm"
include "cdm.mm"
include "chash.mm"
include "csb.mm"
include "cmpt.mm"
include "cwrecs.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "csbeq2dv.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "wrecseq3.mm"
include "syl.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "df-bpoly.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "wwe.mm"
include "cuz.mm"
include "ltweuz.mm"
include "wb.mm"
include "nn0uz.mm"
include "weeq2.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "wse.mm"
include "nn0ex.mm"
include "exse.mm"
include "wfr2.mm"
include "adantr.mm"
include "prednn0.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "wfun.mm"
include "wfrfun.mm"
include "ovex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "dmeq.mm"
include "wfn.mm"
include "wss.mm"
include "wfr1.mm"
include "fz0ssnn0.mm"
include "fnssres.mm"
include "fndm.mm"
include "syl6eq.mm"
include "fveq1.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "sumeq12rdv.mm"
include "csbeq1d.mm"
include "eqtrd.mm"
include "csbex.mm"
include "fvmpt.mm"
include "nfcvd.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "sumeq2sdv.mm"
include "csbiegf.mm"
include "cen.mm"
include "wbr.mm"
include "cz.mm"
include "nn0z.mm"
include "fz01en.mm"
include "cfn.mm"
include "fzfi.mm"
include "hashen.mm"
include "sylibr.mm"
include "hashfz1.mm"
include "elfznn0.mm"
include "simpr.mm"
include "weq.mm"
include "syl2anr.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "syl5eq.mm"
include "3eqtrd.mm"

theorem bpolylem
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vx: setvar x
  let vc: setvar c
  assume bpoly.1: |- G = ( g e. _V |-> [_ ( # ` dom g ) / n ]_ ( ( X ^ n ) - sum_ k e. dom g ( ( n _C k ) x. ( ( g ` k ) / ( ( n - k ) + 1 ) ) ) ) )
  assume bpoly.2: |- F = wrecs ( < , NN0 , G )

  disjoint g k
  disjoint g n
  disjoint F g
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint N g
  disjoint N k
  disjoint N n
  disjoint X g
  disjoint X k
  disjoint X n
  disjoint g m
  disjoint g x
  disjoint k m
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F x
  disjoint N m
  disjoint N x
  disjoint c g
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint X c
  disjoint X m
  disjoint X x
  assert |- ( ( N e. NN0 /\ X e. CC ) -> ( N BernPoly X ) = ( ( X ^ N ) - sum_ k e. ( 0 ... ( N - 1 ) ) ( ( N _C k ) x. ( ( k BernPoly X ) / ( ( N - k ) + 1 ) ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cX
    cc
    wcel
    #
    wa
    #
    cN
    cX
    cbp
    co
    cN
    cF
    cfv
    #
    cF
    cn0
    clt
    cN
    cpred
    #
    cres
    #
    cG
    cfv
    #
    cX
    cN
    cexp
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    @10
    cX
    cbp
    co
    #
    cN
    @10
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    vm
    vx
    cN
    cX
    cn0
    cc
    vm
    cv
    #
    cn0
    clt
    vg
    cvv
    vn
    vg
    cv
    #
    cdm
    #
    chash
    cfv
    #
    vx
    cv
    #
    vn
    cv
    #
    cexp
    co
    #
    @21
    @24
    @10
    cbc
    co
    #
    @10
    @20
    cfv
    #
    @24
    @10
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    csb
    #
    cmpt
    #
    cwrecs
    #
    cfv
    #
    @3
    cbp
    @23
    cX
    wceq
    #
    @19
    cN
    wceq
    @37
    @19
    cF
    cfv
    #
    @3
    @38
    @19
    @36
    cF
    @38
    @36
    cn0
    clt
    cG
    cwrecs
    #
    cF
    @38
    @35
    cG
    wceq
    @36
    @40
    wceq
    @38
    @35
    vg
    cvv
    vn
    @22
    cX
    @24
    cexp
    co
    #
    @32
    cmin
    co
    #
    csb
    #
    cmpt
    cG
    @38
    vg
    cvv
    @34
    @43
    @38
    vn
    @22
    @33
    @42
    @38
    @25
    @41
    @32
    cmin
    @23
    cX
    @24
    cexp
    oveq1
    oveq1d
    csbeq2dv
    mpteq2dv
    bpoly.1
    syl6eqr
    cn0
    clt
    @35
    cG
    wrecseq3
    syl
    bpoly.2
    syl6eqr
    fveq1d
    #
    @19
    cN
    cF
    fveq2
    sylan9eqr
    vx
    vg
    vk
    vm
    vn
    df-bpoly
    #
    cN
    cF
    fvex
    ovmpt2a
    @0
    @3
    @6
    wceq
    @1
    cn0
    clt
    cF
    cG
    cN
    cn0
    clt
    wwe
    #
    cc0
    cuz
    cfv
    #
    clt
    wwe
    #
    cc0
    ltweuz
    cn0
    @47
    wceq
    @46
    @48
    wb
    nn0uz
    cn0
    @47
    clt
    weeq2
    ax-mp
    mpbir
    #
    cn0
    cvv
    wcel
    cn0
    clt
    wse
    nn0ex
    cn0
    clt
    cvv
    exse
    ax-mp
    #
    bpoly.2
    wfr2
    adantr
    @2
    @6
    cF
    @9
    cres
    #
    cG
    cfv
    #
    @18
    @2
    @5
    @51
    cG
    @2
    @4
    @9
    cF
    @0
    @4
    @9
    wceq
    @1
    cN
    prednn0
    adantr
    reseq2d
    fveq2d
    @2
    @52
    vn
    @9
    chash
    cfv
    #
    @41
    @9
    @26
    @10
    cF
    cfv
    #
    @29
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    csb
    #
    @18
    @51
    cvv
    wcel
    #
    @52
    @59
    wceq
    cF
    wfun
    @9
    cvv
    wcel
    @60
    cn0
    clt
    cF
    cG
    @49
    @50
    bpoly.2
    wfrfun
    cc0
    @8
    cfz
    ovex
    cF
    @9
    cvv
    resfunexg
    mp2an
    vg
    @51
    @43
    @59
    cvv
    cG
    @20
    @51
    wceq
    #
    @43
    vn
    @22
    @58
    csb
    @59
    @61
    vn
    @22
    @42
    @58
    @61
    @32
    @57
    @41
    cmin
    @61
    @21
    @9
    @31
    @56
    vk
    @61
    @21
    @51
    cdm
    #
    @9
    @20
    @51
    dmeq
    @51
    @9
    wfn
    #
    @62
    @9
    wceq
    cF
    cn0
    wfn
    @9
    cn0
    wss
    @63
    cn0
    clt
    cF
    cG
    @49
    @50
    bpoly.2
    wfr1
    @8
    fz0ssnn0
    cn0
    @9
    cF
    fnssres
    mp2an
    @9
    @51
    fndm
    ax-mp
    syl6eq
    #
    @61
    @10
    @9
    wcel
    #
    wa
    #
    @30
    @55
    @26
    cmul
    @66
    @27
    @54
    @29
    cdiv
    @61
    @65
    @27
    @10
    @51
    cfv
    @54
    @10
    @20
    @51
    fveq1
    @10
    @9
    cF
    fvres
    sylan9eq
    oveq1d
    oveq2d
    sumeq12rdv
    oveq2d
    csbeq2dv
    @61
    vn
    @22
    @53
    @58
    @61
    @21
    @9
    chash
    @64
    fveq2d
    csbeq1d
    eqtrd
    bpoly.1
    vn
    @53
    @58
    @41
    @57
    cmin
    ovex
    csbex
    fvmpt
    ax-mp
    @2
    vn
    cN
    @58
    csb
    #
    @7
    @9
    @11
    @54
    @14
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    @59
    @18
    @0
    @67
    @71
    wceq
    @1
    vn
    cN
    @58
    @71
    cn0
    @0
    vn
    @71
    nfcvd
    @24
    cN
    wceq
    #
    @41
    @7
    @57
    @70
    cmin
    @24
    cN
    cX
    cexp
    oveq2
    @72
    @9
    @56
    @69
    vk
    @72
    @26
    @11
    @55
    @68
    cmul
    @24
    cN
    @10
    cbc
    oveq1
    @72
    @29
    @14
    @54
    cdiv
    @72
    @28
    @13
    c1
    caddc
    @24
    cN
    @10
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq12d
    sumeq2sdv
    oveq12d
    csbiegf
    adantr
    @2
    vn
    @53
    cN
    @58
    @0
    @53
    cN
    wceq
    @1
    @0
    @53
    c1
    cN
    cfz
    co
    #
    chash
    cfv
    #
    cN
    @0
    @9
    @73
    cen
    wbr
    #
    @53
    @74
    wceq
    #
    @0
    cN
    cz
    wcel
    @75
    cN
    nn0z
    cN
    fz01en
    syl
    @9
    cfn
    wcel
    @73
    cfn
    wcel
    @76
    @75
    wb
    cc0
    @8
    fzfi
    c1
    cN
    fzfi
    @9
    @73
    hashen
    mp2an
    sylibr
    cN
    hashfz1
    eqtrd
    adantr
    csbeq1d
    @2
    @17
    @70
    @7
    cmin
    @2
    @9
    @16
    @69
    vk
    @2
    @65
    wa
    #
    @15
    @68
    @11
    cmul
    @77
    @12
    @54
    @14
    cdiv
    @65
    @10
    cn0
    wcel
    @1
    @12
    @54
    wceq
    @2
    @10
    @8
    elfznn0
    @0
    @1
    simpr
    vm
    vx
    @10
    cX
    cn0
    cc
    @37
    @54
    cbp
    @38
    vm
    vk
    weq
    @37
    @39
    @54
    @44
    @19
    @10
    cF
    fveq2
    sylan9eqr
    @45
    @10
    cF
    fvex
    ovmpt2a
    syl2anr
    oveq1d
    oveq2d
    sumeq2dv
    oveq2d
    3eqtr4d
    syl5eq
    eqtrd
    3eqtrd
end
