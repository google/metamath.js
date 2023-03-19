include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "cprod.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cmin.mm"
include "cmul.mm"
include "cexp.mm"
include "peano2nn0.mm"
include "fmtno.mm"
include "3syl.mm"
include "2cnd.mm"
include "expp1d.mm"
include "oveq2d.mm"
include "2nn0.mm"
include "a1i.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "sqvald.mm"
include "expmuld.mm"
include "fmtnom1nn.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "oveq1.mm"
include "adantl.mm"
include "fzfid.mm"
include "cc.mm"
include "elfznn0.mm"
include "fmtnonn.mm"
include "nncnd.mm"
include "fprodcl.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "cn.mm"
include "subcld.mm"
include "muls1d.mm"
include "mulid2d.mm"
include "joinlmuladdmuld.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "syl6rbbr.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "mulcld.mm"
include "addassd.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "fveq2.mm"
include "fprodp1.mm"
include "eqcomd.mm"
include "npcan1.mm"
include "subadd23d.mm"
include "nncand.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"

theorem fmtnorec2lem
  let vy: setvar y
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k

  disjoint n y
  disjoint n x
  disjoint x y
  disjoint k x
  assert |- ( y e. NN0 -> ( ( FermatNo ` ( y + 1 ) ) = ( prod_ n e. ( 0 ... y ) ( FermatNo ` n ) + 2 ) -> ( FermatNo ` ( ( y + 1 ) + 1 ) ) = ( prod_ n e. ( 0 ... ( y + 1 ) ) ( FermatNo ` n ) + 2 ) ) )

  proof
    vy
    cv
    #
    cn0
    wcel
    #
    @0
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    @0
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
    c2
    caddc
    co
    #
    wceq
    #
    @2
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    @2
    cfz
    co
    #
    @6
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    @1
    @9
    wa
    #
    @11
    @3
    c1
    cmin
    co
    #
    @16
    cmul
    co
    #
    c1
    caddc
    co
    #
    @8
    c1
    cmin
    co
    #
    @16
    cmul
    co
    #
    c1
    caddc
    co
    #
    @14
    @1
    @11
    @18
    wceq
    @9
    @1
    @11
    c2
    c2
    @10
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    @18
    @1
    @2
    cn0
    wcel
    #
    @10
    cn0
    wcel
    @11
    @24
    wceq
    @0
    peano2nn0
    #
    @2
    peano2nn0
    @10
    fmtno
    3syl
    @1
    @23
    @17
    c1
    caddc
    @1
    @23
    c2
    c2
    @2
    cexp
    co
    #
    c2
    cmul
    co
    #
    cexp
    co
    #
    @17
    @1
    @22
    @28
    c2
    cexp
    @1
    c2
    @2
    @1
    2cnd
    #
    @26
    expp1d
    oveq2d
    @1
    c2
    @27
    cexp
    co
    #
    c2
    cexp
    co
    @31
    @31
    cmul
    co
    @29
    @17
    @1
    @31
    @1
    @31
    @1
    c2
    @27
    c2
    cn0
    wcel
    @1
    2nn0
    a1i
    #
    @1
    c2
    @2
    @32
    @26
    nn0expcld
    #
    nn0expcld
    nn0cnd
    sqvald
    @1
    c2
    @27
    c2
    @30
    @32
    @33
    expmuld
    @1
    @16
    @31
    @16
    @31
    cmul
    @1
    @25
    @16
    @31
    wceq
    @26
    @2
    fmtnom1nn
    syl
    #
    @34
    oveq12d
    3eqtr4d
    eqtrd
    oveq1d
    eqtrd
    adantr
    @9
    @18
    @21
    wceq
    @1
    @9
    @17
    @20
    c1
    caddc
    @9
    @16
    @19
    @16
    cmul
    @3
    @8
    c1
    cmin
    oveq1
    oveq1d
    oveq1d
    adantl
    @15
    @21
    @7
    @3
    cmul
    co
    #
    @7
    cmin
    co
    #
    @16
    caddc
    co
    #
    c1
    caddc
    co
    #
    @14
    @15
    @20
    @37
    c1
    caddc
    @1
    @20
    @37
    wceq
    @9
    @1
    @20
    @7
    c1
    caddc
    co
    #
    @16
    cmul
    co
    @37
    @1
    @19
    @39
    @16
    cmul
    @1
    @19
    @7
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @39
    @1
    @7
    c2
    c1
    @1
    @4
    @6
    vn
    @1
    cc0
    @0
    fzfid
    @5
    @4
    wcel
    #
    @6
    cc
    wcel
    #
    @1
    @41
    @5
    cn0
    wcel
    #
    @42
    @5
    @0
    elfznn0
    @43
    @6
    @5
    fmtnonn
    nncnd
    #
    syl
    adantl
    fprodcl
    #
    @30
    @1
    1cnd
    #
    addsubassd
    @40
    c1
    @7
    caddc
    2m1e1
    oveq2i
    syl6eq
    oveq1d
    @1
    @7
    @16
    c1
    @37
    @45
    @1
    @3
    c1
    @1
    @3
    @1
    @25
    @3
    cn
    wcel
    @26
    @2
    fmtnonn
    syl
    nncnd
    #
    @46
    subcld
    #
    @46
    @1
    @7
    @16
    cmul
    co
    @36
    c1
    @16
    cmul
    co
    @16
    caddc
    @1
    @7
    @3
    @45
    @47
    muls1d
    @1
    @16
    @48
    mulid2d
    oveq12d
    joinlmuladdmuld
    eqtrd
    adantr
    oveq1d
    @1
    @9
    @38
    @14
    wceq
    #
    @1
    @9
    @3
    c2
    cmin
    co
    #
    @7
    wceq
    #
    @49
    @1
    @51
    @8
    @3
    wceq
    @9
    @1
    @3
    c2
    @7
    @47
    @30
    @45
    subadd2d
    @3
    @8
    eqcom
    syl6rbbr
    @1
    @51
    @49
    @51
    @1
    @38
    @35
    @50
    cmin
    co
    #
    @16
    caddc
    co
    #
    c1
    caddc
    co
    #
    @14
    @38
    @54
    wceq
    @7
    @50
    @7
    @50
    wceq
    #
    @37
    @53
    c1
    caddc
    @55
    @36
    @52
    @16
    caddc
    @7
    @50
    @35
    cmin
    oveq2
    oveq1d
    oveq1d
    eqcoms
    @1
    @54
    @52
    @16
    c1
    caddc
    co
    #
    caddc
    co
    #
    @13
    @3
    @50
    cmin
    co
    #
    caddc
    co
    #
    @14
    @1
    @52
    @16
    c1
    @1
    @35
    @50
    @1
    @7
    @3
    @45
    @47
    mulcld
    @1
    @3
    c2
    @47
    @30
    subcld
    #
    subcld
    @48
    @46
    addassd
    @1
    @57
    @13
    @50
    cmin
    co
    #
    @3
    caddc
    co
    @59
    @1
    @52
    @61
    @56
    @3
    caddc
    @1
    @35
    @13
    @50
    cmin
    @1
    @13
    @35
    @1
    @6
    @3
    vn
    cc0
    @0
    @1
    @0
    cc0
    cuz
    cfv
    wcel
    @0
    elnn0uz
    biimpi
    @5
    @12
    wcel
    #
    @42
    @1
    @62
    @43
    @42
    @5
    @2
    elfznn0
    @44
    syl
    adantl
    #
    @5
    @2
    cfmtno
    fveq2
    fprodp1
    eqcomd
    oveq1d
    @1
    @3
    cc
    wcel
    @56
    @3
    wceq
    @47
    @3
    npcan1
    syl
    oveq12d
    @1
    @13
    @50
    @3
    @1
    @12
    @6
    vn
    @1
    cc0
    @2
    fzfid
    @63
    fprodcl
    @60
    @47
    subadd23d
    eqtrd
    @1
    @58
    c2
    @13
    caddc
    @1
    @3
    c2
    @47
    @30
    nncand
    oveq2d
    3eqtrd
    sylan9eqr
    ex
    sylbid
    imp
    eqtrd
    3eqtrd
    ex
end
