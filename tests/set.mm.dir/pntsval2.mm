include "cr.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "clog.mm"
include "cdiv.mm"
include "cchp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "pntsval.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "recnd.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "simpl.mm"
include "nndivred.mm"
include "chpcl.mm"
include "adddid.mm"
include "sumeq2dv.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "fzfid.mm"
include "fsummulc2.mm"
include "chpval.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "ad2antlr.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "3eqtr4d.mm"
include "oveq1.mm"
include "id.mm"
include "cc.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "dvdsdivcl.mm"
include "sylan.mm"
include "remulcld.mm"
include "anasss.mm"
include "dvdsflsumcom.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "mulcld.mm"
include "fsumadd.mm"
include "cfn.mm"
include "wss.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fsumrecl.mm"
include "3eqtrd.mm"

theorem pntsval2
  let vy: setvar y
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let cB: class B
  let wph: wff ph
  let cR: class R
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )

  disjoint a i
  disjoint a m
  disjoint a n
  disjoint a y
  disjoint A a
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint A i
  disjoint m n
  disjoint m y
  disjoint A m
  disjoint n y
  disjoint A n
  disjoint A y
  disjoint S m
  disjoint S n
  disjoint S y
  disjoint a c
  disjoint a k
  disjoint a x
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m x
  disjoint n x
  disjoint x y
  disjoint A x
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint S c
  disjoint S k
  disjoint S x
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- ( A e. RR -> ( S ` A ) = sum_ n e. ( 1 ... ( |_ ` A ) ) ( ( ( Lam ` n ) x. ( log ` n ) ) + sum_ m e. { y e. NN | y || n } ( ( Lam ` m ) x. ( Lam ` ( n / m ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cS
    cfv
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    cA
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    cmul
    co
    #
    vn
    csu
    @2
    @4
    @5
    cmul
    co
    #
    @4
    @7
    cmul
    co
    #
    caddc
    co
    #
    vn
    csu
    #
    @2
    @9
    vy
    cv
    @3
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    vm
    cv
    #
    cvma
    cfv
    #
    @3
    @15
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    caddc
    co
    vn
    csu
    #
    cA
    cS
    vi
    vn
    va
    pntsval.1
    pntsval
    @0
    @2
    @8
    @11
    vn
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @5
    @7
    @23
    @4
    @23
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @22
    @24
    @0
    @3
    @1
    elfznn
    adantl
    #
    @3
    vmacl
    syl
    recnd
    #
    @23
    @5
    @23
    @3
    @23
    @3
    @25
    nnrpd
    relogcld
    recnd
    #
    @23
    @7
    @23
    @6
    cr
    wcel
    @7
    cr
    wcel
    @23
    cA
    @3
    @0
    @22
    simpl
    @25
    nndivred
    @6
    chpcl
    syl
    recnd
    #
    adddid
    sumeq2dv
    @0
    @2
    @9
    vn
    csu
    #
    @2
    @10
    vn
    csu
    #
    caddc
    co
    @29
    @2
    @20
    vn
    csu
    #
    caddc
    co
    @12
    @21
    @0
    @30
    @31
    @29
    caddc
    @0
    @30
    @2
    @16
    cA
    @15
    cdiv
    co
    #
    cchp
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    @31
    @2
    @10
    @34
    vn
    vm
    @3
    @15
    wceq
    #
    @4
    @16
    @7
    @33
    cmul
    @3
    @15
    cvma
    fveq2
    @36
    @6
    @32
    cchp
    @3
    @15
    cA
    cdiv
    oveq2
    fveq2d
    oveq12d
    cbvsumv
    @0
    @35
    @2
    c1
    @32
    cfl
    cfv
    #
    cfz
    co
    #
    @16
    @15
    vk
    cv
    #
    cmul
    co
    #
    @15
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    vm
    csu
    @31
    @0
    @2
    @34
    @44
    vm
    @0
    @15
    @2
    wcel
    #
    wa
    #
    @16
    @38
    @39
    cvma
    cfv
    #
    vk
    csu
    #
    cmul
    co
    @38
    @16
    @47
    cmul
    co
    #
    vk
    csu
    @34
    @44
    @46
    @38
    @47
    @16
    vk
    @46
    c1
    @37
    fzfid
    @46
    @16
    @46
    @15
    cn
    wcel
    #
    @16
    cr
    wcel
    #
    @45
    @50
    @0
    @15
    @1
    elfznn
    #
    adantl
    #
    @15
    vmacl
    #
    syl
    recnd
    @46
    @39
    @38
    wcel
    #
    wa
    #
    @47
    @56
    @39
    cn
    wcel
    #
    @47
    cr
    wcel
    @55
    @57
    @46
    @39
    @37
    elfznn
    adantl
    #
    @39
    vmacl
    syl
    recnd
    fsummulc2
    @46
    @33
    @48
    @16
    cmul
    @46
    @32
    cr
    wcel
    @33
    @48
    wceq
    @46
    cA
    @15
    @0
    @45
    simpl
    @53
    nndivred
    @32
    vk
    chpval
    syl
    oveq2d
    @46
    @38
    @43
    @49
    vk
    @56
    @42
    @47
    @16
    cmul
    @56
    @41
    @39
    cvma
    @56
    @39
    @15
    @56
    @39
    @58
    nncnd
    @56
    @15
    @45
    @50
    @0
    @55
    @52
    ad2antlr
    #
    nncnd
    @56
    @15
    @59
    nnne0d
    divcan3d
    fveq2d
    oveq2d
    sumeq2dv
    3eqtr4d
    sumeq2dv
    @0
    vy
    cA
    @19
    @43
    vk
    vn
    vm
    @3
    @40
    wceq
    #
    @18
    @42
    @16
    cmul
    @60
    @17
    @41
    cvma
    @3
    @40
    @15
    cdiv
    oveq1
    fveq2d
    oveq2d
    @0
    id
    @0
    @22
    @15
    @14
    wcel
    #
    @19
    cc
    wcel
    @23
    @61
    wa
    #
    @19
    @62
    @16
    @18
    @62
    @50
    @51
    @62
    @14
    cn
    @15
    @13
    vy
    cn
    ssrab2
    #
    @23
    @61
    simpr
    sseldi
    @54
    syl
    @62
    @17
    cn
    wcel
    @18
    cr
    wcel
    @62
    @14
    cn
    @17
    @63
    @23
    @24
    @61
    @17
    @14
    wcel
    @25
    vy
    @15
    @3
    dvdsdivcl
    sylan
    sseldi
    @17
    vmacl
    syl
    remulcld
    #
    recnd
    anasss
    dvdsflsumcom
    eqtr4d
    syl5eq
    oveq2d
    @0
    @2
    @9
    @10
    vn
    @0
    c1
    @1
    fzfid
    #
    @23
    @4
    @5
    @26
    @27
    mulcld
    #
    @23
    @4
    @7
    @26
    @28
    mulcld
    fsumadd
    @0
    @2
    @9
    @20
    vn
    @65
    @66
    @23
    @20
    @23
    @14
    @19
    vm
    @23
    c1
    @3
    cfz
    co
    #
    cfn
    wcel
    @14
    @67
    wss
    #
    @14
    cfn
    wcel
    @23
    c1
    @3
    fzfid
    @23
    @24
    @68
    @25
    @3
    vy
    dvdsssfz1
    syl
    @67
    @14
    ssfi
    syl2anc
    @64
    fsumrecl
    recnd
    fsumadd
    3eqtr4d
    3eqtrd
end
