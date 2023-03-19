include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfmtno.mm"
include "cexp.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cmul.mm"
include "caddc.mm"
include "fzfid.mm"
include "cc.mm"
include "cn0.mm"
include "cn.mm"
include "elfznn0.mm"
include "fmtnonn.mm"
include "syl.mm"
include "nncnd.mm"
include "adantl.mm"
include "fprodcl.mm"
include "2cn.mm"
include "a1i.mm"
include "wceq.mm"
include "uznn0sub.mm"
include "fmtnorec2.mm"
include "eqcomd.mm"
include "mvlraddd.mm"
include "oveq2d.mm"
include "2nn0.mm"
include "eluz2nn.mm"
include "nnm1nn0.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "peano2nn0.mm"
include "subdid.mm"
include "eluzelcn.mm"
include "ax-1cn.mm"
include "w3a.mm"
include "subsub.mm"
include "syl3anc.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "mulid2d.mm"
include "adddird.mm"
include "addcomd.mm"
include "fmtno.mm"
include "eqtr4d.mm"
include "sqvald.mm"
include "3eqtr2d.mm"
include "mulcld.mm"
include "addsubassd.mm"
include "npcan1.mm"
include "fmtnorec1.mm"
include "binom2sub1.mm"
include "nnsqcld.mm"
include "subcld.mm"
include "addassd.mm"
include "2timesi.mm"
include "eqcomi.mm"
include "mulcli.mm"
include "subadd23d.mm"
include "cneg.mm"
include "mulneg2d.mm"
include "negsubdi2d.mm"
include "fmtnom1nn.mm"
include "eqtr3d.mm"
include "subnegd.mm"
include "mulcomd.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "3eqtrrd.mm"

theorem fmtnorec3
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vx: setvar x

  disjoint N n
  disjoint k x
  assert |- ( N e. ( ZZ>= ` 2 ) -> ( FermatNo ` N ) = ( ( FermatNo ` ( N - 1 ) ) + ( ( 2 ^ ( 2 ^ ( N - 1 ) ) ) x. prod_ n e. ( 0 ... ( N - 2 ) ) ( FermatNo ` n ) ) ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cfmtno
    cfv
    #
    c2
    c2
    @1
    cexp
    co
    #
    cexp
    co
    #
    cc0
    cN
    c2
    cmin
    co
    #
    cfz
    co
    #
    vn
    cv
    #
    cfmtno
    cfv
    #
    vn
    cprod
    #
    cmul
    co
    #
    caddc
    co
    @2
    @4
    @5
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    c2
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    @2
    @4
    @2
    cmul
    co
    #
    @4
    c2
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cN
    cfmtno
    cfv
    #
    @0
    @10
    @14
    @2
    caddc
    @0
    @9
    @13
    @4
    cmul
    @0
    @9
    c2
    @12
    @0
    @6
    @8
    vn
    @0
    cc0
    @5
    fzfid
    @7
    @6
    wcel
    #
    @8
    cc
    wcel
    @0
    @20
    @8
    @20
    @7
    cn0
    wcel
    @8
    cn
    wcel
    @7
    @5
    elfznn0
    @7
    fmtnonn
    syl
    nncnd
    adantl
    fprodcl
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    #
    @0
    @12
    @9
    c2
    caddc
    co
    #
    @0
    @5
    cn0
    wcel
    #
    @12
    @23
    wceq
    c2
    cN
    uznn0sub
    #
    vn
    @5
    fmtnorec2
    syl
    eqcomd
    mvlraddd
    oveq2d
    oveq2d
    @0
    @14
    @17
    @2
    caddc
    @0
    @14
    @4
    @12
    cmul
    co
    #
    @16
    cmin
    co
    @17
    @0
    @4
    @12
    c2
    @0
    @4
    @0
    c2
    @3
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    #
    @0
    c2
    @1
    @27
    @0
    cN
    cn
    wcel
    @1
    cn0
    wcel
    #
    cN
    eluz2nn
    cN
    nnm1nn0
    syl
    #
    nn0expcld
    nn0expcld
    nn0cnd
    #
    @0
    @12
    @0
    @11
    cn0
    wcel
    #
    @12
    cn
    wcel
    @0
    @24
    @31
    @25
    @5
    peano2nn0
    syl
    @11
    fmtnonn
    syl
    nncnd
    @22
    subdid
    @0
    @26
    @15
    @16
    cmin
    @0
    @12
    @2
    @4
    cmul
    @0
    @11
    @1
    cfmtno
    @0
    @11
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @1
    @0
    cN
    cc
    wcel
    #
    @21
    c1
    cc
    wcel
    #
    @11
    @33
    wceq
    c2
    cN
    eluzelcn
    #
    @22
    @35
    @0
    ax-1cn
    a1i
    #
    @34
    @21
    @35
    w3a
    @33
    @11
    cN
    c2
    c1
    subsub
    eqcomd
    syl3anc
    @32
    c1
    cN
    cmin
    2m1e1
    oveq2i
    syl6eq
    fveq2d
    oveq2d
    oveq1d
    eqtrd
    oveq2d
    @0
    @2
    @15
    caddc
    co
    #
    @16
    cmin
    co
    @2
    c2
    cexp
    co
    #
    @16
    cmin
    co
    #
    @18
    @19
    @0
    @38
    @39
    @16
    cmin
    @0
    @38
    c1
    @2
    cmul
    co
    #
    @15
    caddc
    co
    c1
    @4
    caddc
    co
    #
    @2
    cmul
    co
    #
    @39
    @0
    @2
    @41
    @15
    caddc
    @0
    @41
    @2
    @0
    @2
    @0
    @2
    @0
    @28
    @2
    cn
    wcel
    @29
    @1
    fmtnonn
    syl
    #
    nncnd
    #
    mulid2d
    eqcomd
    oveq1d
    @0
    c1
    @4
    @2
    @37
    @30
    @45
    adddird
    @0
    @43
    @2
    @2
    cmul
    co
    @39
    @0
    @42
    @2
    @2
    cmul
    @0
    @42
    @4
    c1
    caddc
    co
    #
    @2
    @0
    c1
    @4
    @37
    @30
    addcomd
    @0
    @28
    @2
    @46
    wceq
    @29
    @1
    fmtno
    syl
    eqtr4d
    oveq1d
    @0
    @2
    @45
    sqvald
    eqtr4d
    3eqtr2d
    oveq1d
    @0
    @2
    @15
    @16
    @45
    @0
    @4
    @2
    @30
    @45
    mulcld
    @0
    @4
    c2
    @30
    @22
    mulcld
    addsubassd
    @0
    @19
    @1
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    @2
    c1
    cmin
    co
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    @40
    @0
    cN
    @47
    cfmtno
    @0
    @47
    cN
    @0
    @34
    @47
    cN
    wceq
    @36
    cN
    npcan1
    syl
    eqcomd
    fveq2d
    @0
    @28
    @48
    @51
    wceq
    @29
    @1
    fmtnorec1
    syl
    @0
    @51
    @39
    c2
    @2
    cmul
    co
    #
    cmin
    co
    #
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    @53
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @40
    @0
    @50
    @54
    c1
    caddc
    @0
    @2
    cc
    wcel
    @50
    @54
    wceq
    @45
    @2
    binom2sub1
    syl
    oveq1d
    @0
    @55
    @53
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @57
    @0
    @53
    c1
    c1
    @0
    @39
    @52
    @0
    @39
    @0
    @2
    @44
    nnsqcld
    nncnd
    #
    @0
    c2
    @2
    @22
    @45
    mulcld
    #
    subcld
    @37
    @37
    addassd
    @0
    @58
    @56
    @53
    caddc
    @58
    @56
    wceq
    @0
    @56
    @58
    c1
    ax-1cn
    2timesi
    eqcomi
    a1i
    oveq2d
    eqtrd
    @0
    @57
    @39
    @56
    @52
    cmin
    co
    #
    caddc
    co
    @39
    c2
    c1
    @2
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @40
    @0
    @39
    @52
    @56
    @59
    @60
    @56
    cc
    wcel
    @0
    c2
    c1
    2cn
    ax-1cn
    mulcli
    a1i
    subadd23d
    @0
    @61
    @63
    @39
    caddc
    @0
    @63
    @61
    @0
    c2
    c1
    @2
    @22
    @37
    @45
    subdid
    eqcomd
    oveq2d
    @0
    @39
    @63
    cneg
    #
    cmin
    co
    @39
    c2
    @4
    cmul
    co
    #
    cmin
    co
    @64
    @40
    @0
    @65
    @66
    @39
    cmin
    @0
    c2
    @62
    cneg
    #
    cmul
    co
    @65
    @66
    @0
    c2
    @62
    @22
    @0
    c1
    @2
    @37
    @45
    subcld
    #
    mulneg2d
    @0
    @67
    @4
    c2
    cmul
    @0
    @67
    @49
    @4
    @0
    c1
    @2
    @37
    @45
    negsubdi2d
    @0
    @28
    @49
    @4
    wceq
    @29
    @1
    fmtnom1nn
    syl
    eqtrd
    oveq2d
    eqtr3d
    oveq2d
    @0
    @39
    @63
    @59
    @0
    c2
    @62
    @22
    @68
    mulcld
    subnegd
    @0
    @66
    @16
    @39
    cmin
    @0
    c2
    @4
    @22
    @30
    mulcomd
    oveq2d
    3eqtr3d
    3eqtrd
    3eqtrd
    3eqtrrd
    3eqtr3d
    3eqtrrd
end
