include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wrex.mm"
include "cc.mm"
include "wi.mm"
include "1re.mm"
include "ax-rnegex.mm"
include "wa.mm"
include "cmul.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "ci.mm"
include "ax-icn.mm"
include "mulcli.mm"
include "ax-1cn.mm"
include "0cn.mm"
include "adddii.mm"
include "mulid1i.mm"
include "mul01.mm"
include "ax-mp.mm"
include "ax-i2m1.mm"
include "eqtr4i.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "eqeq12i.mm"
include "addassi.mm"
include "oveq2i.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "00id.mm"
include "eqcomi.mm"
include "wb.mm"
include "0re.mm"
include "readdcan.mm"
include "mp3an.mm"
include "3bitri.mm"
include "sylib.mm"
include "syl6.mm"
include "necon3d.mm"
include "mpi.mm"
include "ax-rrecex.mm"
include "sylan2.mm"
include "simpr.mm"
include "simplrl.mm"
include "recnd.mm"
include "mulcld.mm"
include "simplll.mm"
include "a1i.mm"
include "adddid.mm"
include "addassd.mm"
include "simpllr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "3eqtr4a.mm"
include "readdcld.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "mul31.mm"
include "simplrr.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "exp42.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "rexlimiva.mm"
include "mp2b.mm"

theorem addid1
  let cA: class A
  let vc: setvar c
  let vx: setvar x


  assert |- ( A e. CC -> ( A + 0 ) = A )

  proof
    c1
    cr
    wcel
    #
    c1
    vc
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vc
    cr
    wrex
    cA
    cc
    wcel
    #
    cA
    cc0
    caddc
    co
    #
    cA
    wceq
    #
    wi
    #
    1re
    vc
    c1
    ax-rnegex
    @3
    @7
    vc
    cr
    @1
    cr
    wcel
    #
    @3
    wa
    #
    @1
    vx
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    #
    @7
    @3
    @8
    @1
    cc0
    wne
    #
    @13
    @3
    c1
    cc0
    wne
    @14
    ax-1ne0
    @3
    @1
    cc0
    c1
    cc0
    @3
    @1
    cc0
    wceq
    #
    c1
    cc0
    caddc
    co
    #
    cc0
    wceq
    #
    c1
    cc0
    wceq
    #
    @15
    @3
    @17
    @15
    @2
    @16
    cc0
    @1
    cc0
    c1
    caddc
    oveq2
    eqeq1d
    biimpcd
    @17
    ci
    ci
    cmul
    co
    #
    @19
    cmul
    co
    #
    @16
    cmul
    co
    #
    @20
    cc0
    cmul
    co
    #
    wceq
    #
    @18
    @16
    cc0
    @20
    cmul
    oveq2
    @23
    @20
    @19
    c1
    caddc
    co
    #
    caddc
    co
    #
    cc0
    wceq
    cc0
    c1
    caddc
    co
    #
    cc0
    cc0
    caddc
    co
    #
    wceq
    #
    @18
    @21
    @25
    @22
    cc0
    @21
    @20
    c1
    cmul
    co
    #
    @22
    caddc
    co
    @25
    @20
    c1
    cc0
    @19
    @19
    ci
    ci
    ax-icn
    ax-icn
    mulcli
    #
    @30
    mulcli
    #
    ax-1cn
    0cn
    adddii
    @29
    @20
    @22
    @24
    caddc
    @20
    @31
    mulid1i
    @22
    cc0
    @24
    @20
    cc
    wcel
    @22
    cc0
    wceq
    @31
    @20
    mul01
    ax-mp
    #
    ax-i2m1
    eqtr4i
    oveq12i
    eqtri
    @32
    eqeq12i
    @25
    @26
    cc0
    @27
    @20
    @19
    caddc
    co
    #
    c1
    caddc
    co
    @25
    @26
    @20
    @19
    c1
    @31
    @30
    ax-1cn
    addassi
    @33
    cc0
    c1
    caddc
    @20
    @19
    c1
    cmul
    co
    #
    caddc
    co
    #
    @33
    cc0
    @34
    @19
    @20
    caddc
    @19
    @30
    mulid1i
    oveq2i
    @19
    @24
    cmul
    co
    #
    @35
    cc0
    @19
    @19
    c1
    @30
    @30
    ax-1cn
    adddii
    @36
    @19
    cc0
    cmul
    co
    #
    cc0
    @24
    cc0
    @19
    cmul
    ax-i2m1
    oveq2i
    @19
    cc
    wcel
    @37
    cc0
    wceq
    @30
    @19
    mul01
    ax-mp
    eqtri
    eqtr3i
    eqtr3i
    oveq1i
    eqtr3i
    @27
    cc0
    00id
    eqcomi
    eqeq12i
    @0
    cc0
    cr
    wcel
    #
    @38
    @28
    @18
    wb
    1re
    0re
    0re
    c1
    cc0
    cc0
    readdcan
    mp3an
    3bitri
    sylib
    syl6
    necon3d
    mpi
    vx
    @1
    ax-rrecex
    sylan2
    @9
    @12
    @7
    vx
    cr
    @9
    @10
    cr
    wcel
    #
    @12
    @4
    @6
    @9
    @39
    @12
    wa
    #
    wa
    #
    @4
    wa
    #
    cA
    @10
    cmul
    co
    #
    @1
    cmul
    co
    #
    @43
    cc0
    cmul
    co
    #
    caddc
    co
    #
    @44
    @5
    cA
    @42
    @43
    @1
    cc0
    caddc
    co
    #
    cmul
    co
    @46
    @44
    @42
    @43
    @1
    cc0
    @42
    cA
    @10
    @41
    @4
    simpr
    #
    @42
    @10
    @9
    @39
    @12
    @4
    simplrl
    recnd
    #
    mulcld
    #
    @42
    @1
    @8
    @3
    @40
    @4
    simplll
    #
    recnd
    #
    cc0
    cc
    wcel
    @42
    0cn
    a1i
    #
    adddid
    @42
    @47
    @1
    @43
    cmul
    @42
    c1
    @47
    caddc
    co
    #
    @2
    wceq
    #
    @47
    @1
    wceq
    #
    @42
    @27
    cc0
    @54
    @2
    00id
    @42
    @2
    cc0
    caddc
    co
    @54
    @27
    @42
    c1
    @1
    cc0
    c1
    cc
    wcel
    @42
    ax-1cn
    a1i
    @52
    @53
    addassd
    @42
    @2
    cc0
    cc0
    caddc
    @8
    @3
    @40
    @4
    simpllr
    #
    oveq1d
    eqtr3d
    @57
    3eqtr4a
    @42
    @47
    cr
    wcel
    @8
    @0
    @55
    @56
    wb
    @42
    @1
    cc0
    @51
    @38
    @42
    0re
    a1i
    readdcld
    @51
    @0
    @42
    1re
    a1i
    @47
    @1
    c1
    readdcan
    syl3anc
    mpbid
    oveq2d
    eqtr3d
    @42
    @44
    cA
    @45
    cc0
    caddc
    @42
    @44
    @11
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    cA
    @42
    @4
    @10
    cc
    wcel
    @1
    cc
    wcel
    @44
    @58
    wceq
    @48
    @49
    @52
    cA
    @10
    @1
    mul31
    syl3anc
    @42
    @11
    c1
    cA
    cmul
    @9
    @39
    @12
    @4
    simplrr
    oveq1d
    @42
    cA
    @48
    mulid2d
    3eqtrd
    #
    @42
    @43
    cc
    wcel
    @45
    cc0
    wceq
    @50
    @43
    mul01
    syl
    oveq12d
    @59
    3eqtr3d
    exp42
    rexlimdv
    mpd
    rexlimiva
    mp2b
end
