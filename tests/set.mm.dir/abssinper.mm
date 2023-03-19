include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cpi.mm"
include "cmul.mm"
include "caddc.mm"
include "csin.mm"
include "cfv.mm"
include "cabs.mm"
include "wceq.mm"
include "c1.mm"
include "zcn.mm"
include "halfcl.mm"
include "2cn.mm"
include "picn.mm"
include "mulass.mm"
include "mp3an23.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan1.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "adantl.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "adantr.mm"
include "sinper.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "cneg.mm"
include "cmin.mm"
include "peano2cn.mm"
include "mulcli.mm"
include "mulcl.mm"
include "sylancl.mm"
include "subadd23.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "ax-1cn.mm"
include "adddir.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "eqtr2d.mm"
include "mpan2.mm"
include "pncan.mm"
include "subcl.mm"
include "sylan.mm"
include "sinmpi.mm"
include "ad2antrr.mm"
include "sincl.mm"
include "absnegd.mm"
include "wo.mm"
include "zeo.mm"
include "mpjaodan.mm"

theorem abssinper
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. ZZ ) -> ( abs ` ( sin ` ( A + ( K x. _pi ) ) ) ) = ( abs ` ( sin ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    cK
    cpi
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    cabs
    cfv
    #
    cA
    csin
    cfv
    #
    cabs
    cfv
    #
    wceq
    cK
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @2
    @4
    wa
    #
    @7
    @9
    cabs
    @14
    @7
    cA
    @3
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    @9
    @2
    @7
    @18
    wceq
    @4
    @2
    @18
    @7
    @2
    @17
    @6
    csin
    @2
    @16
    @5
    cA
    caddc
    @1
    @16
    @5
    wceq
    #
    @0
    @1
    cK
    cc
    wcel
    #
    @19
    cK
    zcn
    #
    @20
    @3
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    #
    @16
    @5
    @20
    @3
    cc
    wcel
    #
    @23
    @16
    wceq
    #
    cK
    halfcl
    @24
    c2
    cc
    wcel
    #
    cpi
    cc
    wcel
    #
    @25
    2cn
    picn
    @3
    c2
    cpi
    mulass
    mp3an23
    syl
    @20
    @22
    cK
    cpi
    cmul
    @20
    @26
    c2
    cc0
    wne
    #
    @22
    cK
    wceq
    2cn
    2ne0
    cK
    c2
    divcan1
    mp3an23
    oveq1d
    eqtr3d
    syl
    adantl
    oveq2d
    fveq2d
    eqcomd
    adantr
    @0
    @4
    @18
    @9
    wceq
    @1
    cA
    @3
    sinper
    adantlr
    eqtrd
    fveq2d
    @2
    @13
    wa
    #
    @8
    @9
    cneg
    #
    cabs
    cfv
    #
    @10
    @29
    @7
    @30
    cabs
    @29
    @7
    cA
    cpi
    cmin
    co
    #
    @12
    @15
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    @30
    @2
    @7
    @35
    wceq
    @13
    @2
    @6
    @34
    csin
    @1
    @0
    @20
    @6
    @34
    wceq
    @21
    @0
    @20
    wa
    #
    @34
    cA
    @33
    cpi
    cmin
    co
    #
    caddc
    co
    #
    @6
    @20
    @0
    @33
    cc
    wcel
    #
    @34
    @38
    wceq
    #
    @20
    @12
    cc
    wcel
    #
    @15
    cc
    wcel
    @39
    @20
    @11
    cc
    wcel
    #
    @41
    cK
    peano2cn
    #
    @11
    halfcl
    syl
    #
    c2
    cpi
    2cn
    picn
    mulcli
    @12
    @15
    mulcl
    sylancl
    @0
    @27
    @39
    @40
    picn
    cA
    cpi
    @33
    subadd23
    mp3an2
    sylan2
    @36
    @37
    @5
    cA
    caddc
    @20
    @37
    @5
    wceq
    @0
    @20
    @37
    @5
    cpi
    caddc
    co
    #
    cpi
    cmin
    co
    #
    @5
    @20
    @33
    @45
    cpi
    cmin
    @20
    @45
    @12
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    #
    @33
    @20
    @48
    @5
    c1
    cpi
    cmul
    co
    #
    caddc
    co
    #
    @45
    @20
    @48
    @11
    cpi
    cmul
    co
    #
    @50
    @20
    @47
    @11
    cpi
    cmul
    @20
    @42
    @47
    @11
    wceq
    #
    @43
    @42
    @26
    @28
    @52
    2cn
    2ne0
    @11
    c2
    divcan1
    mp3an23
    syl
    oveq1d
    @20
    c1
    cc
    wcel
    @27
    @51
    @50
    wceq
    ax-1cn
    picn
    cK
    c1
    cpi
    adddir
    mp3an23
    eqtrd
    @49
    cpi
    @5
    caddc
    cpi
    picn
    mulid2i
    oveq2i
    syl6req
    @20
    @41
    @48
    @33
    wceq
    #
    @44
    @41
    @26
    @27
    @53
    2cn
    picn
    @12
    c2
    cpi
    mulass
    mp3an23
    syl
    eqtr2d
    oveq1d
    @20
    @5
    cc
    wcel
    #
    @27
    @46
    @5
    wceq
    @20
    @27
    @54
    picn
    cK
    cpi
    mulcl
    mpan2
    picn
    @5
    cpi
    pncan
    sylancl
    eqtrd
    adantl
    oveq2d
    eqtr2d
    sylan2
    fveq2d
    adantr
    @29
    @35
    @32
    csin
    cfv
    #
    @30
    @0
    @13
    @35
    @55
    wceq
    #
    @1
    @0
    @32
    cc
    wcel
    #
    @13
    @56
    @0
    @27
    @57
    picn
    cA
    cpi
    subcl
    mpan2
    @32
    @12
    sinper
    sylan
    adantlr
    @0
    @55
    @30
    wceq
    @1
    @13
    cA
    sinmpi
    ad2antrr
    eqtrd
    eqtrd
    fveq2d
    @0
    @31
    @10
    wceq
    @1
    @13
    @0
    @9
    cA
    sincl
    absnegd
    ad2antrr
    eqtrd
    @1
    @4
    @13
    wo
    @0
    cK
    zeo
    adantl
    mpjaodan
end
