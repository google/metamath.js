include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cpi.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simpr.mm"
include "wb.mm"
include "2z.mm"
include "simpl.mm"
include "divides.mm"
include "sylancr.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "cc0.mm"
include "caddc.mm"
include "cc.mm"
include "zcn.mm"
include "negcl.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "a1i.mm"
include "mulcld.mm"
include "addid2d.mm"
include "2cnd.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "id.mm"
include "mulneg1d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "syl.mm"
include "adantr.mm"
include "mulneg12.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "adantl.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "3adant1.mm"
include "0cnd.mm"
include "znegcl.mm"
include "cosper.mm"
include "3ad2ant2.mm"
include "iftrue.mm"
include "cos0.mm"
include "syl6reqr.mm"
include "3ad2ant1.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "wn.mm"
include "odd2np1.mm"
include "biimpa.mm"
include "1cnd.mm"
include "negpicn.mm"
include "adddird.mm"
include "mulneg2d.mm"
include "mulcomd.mm"
include "eqtr3d.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "3adant1r.mm"
include "iffalse.mm"
include "cosnegpi.mm"
include "rexlimdv3a.mm"
include "pm2.61dan.mm"

theorem cosknegpi
  let cK: class K
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( K e. ZZ -> ( cos ` ( K x. -u _pi ) ) = if ( 2 || K , 1 , -u 1 ) )

  proof
    cK
    cz
    wcel
    #
    c2
    cK
    cdvds
    wbr
    #
    cK
    cpi
    cneg
    #
    cmul
    co
    #
    ccos
    cfv
    #
    @1
    c1
    c1
    cneg
    #
    cif
    #
    wceq
    #
    @0
    @1
    wa
    #
    vn
    cv
    #
    c2
    cmul
    co
    #
    cK
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    @8
    @1
    @12
    @0
    @1
    simpr
    @8
    c2
    cz
    wcel
    @0
    @1
    @12
    wb
    2z
    @0
    @1
    simpl
    vn
    c2
    cK
    divides
    sylancr
    mpbid
    @8
    @11
    @7
    vn
    cz
    @1
    @9
    cz
    wcel
    #
    @11
    @7
    wi
    wi
    @0
    @1
    @13
    @11
    @7
    @1
    @13
    @11
    w3a
    @4
    cc0
    @9
    cneg
    #
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
    ccos
    cfv
    #
    cc0
    ccos
    cfv
    #
    @6
    @13
    @11
    @4
    @18
    wceq
    @1
    @13
    @11
    wa
    #
    @3
    @17
    ccos
    @20
    @17
    @10
    cneg
    #
    cpi
    cmul
    co
    #
    @10
    @2
    cmul
    co
    #
    @3
    @13
    @17
    @22
    wceq
    #
    @11
    @13
    @9
    cc
    wcel
    #
    @24
    @9
    zcn
    #
    @25
    @17
    @16
    @14
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    #
    @22
    @25
    @16
    @25
    @14
    @15
    @9
    negcl
    #
    @15
    cc
    wcel
    @25
    c2
    cpi
    2cn
    picn
    mulcli
    a1i
    mulcld
    #
    addid2d
    @25
    @28
    @16
    @25
    @14
    c2
    cpi
    @29
    @25
    2cnd
    #
    cpi
    cc
    wcel
    #
    @25
    picn
    a1i
    #
    mulassd
    #
    eqcomd
    @25
    @27
    @21
    cpi
    cmul
    @25
    @9
    c2
    @25
    id
    #
    @31
    mulneg1d
    oveq1d
    3eqtrd
    syl
    adantr
    @13
    @22
    @23
    wceq
    #
    @11
    @13
    @25
    @36
    @26
    @25
    @10
    cc
    wcel
    @32
    @36
    @25
    @9
    c2
    @35
    @31
    mulcld
    @33
    @10
    cpi
    mulneg12
    syl2anc
    syl
    adantr
    @11
    @23
    @3
    wceq
    @13
    @10
    cK
    @2
    cmul
    oveq1
    adantl
    3eqtrrd
    fveq2d
    3adant1
    @13
    @1
    @18
    @19
    wceq
    #
    @11
    @13
    cc0
    cc
    wcel
    @14
    cz
    wcel
    #
    @37
    @13
    0cnd
    @9
    znegcl
    #
    cc0
    @14
    cosper
    syl2anc
    3ad2ant2
    @1
    @13
    @19
    @6
    wceq
    @11
    @1
    @6
    c1
    @19
    @1
    c1
    @5
    iftrue
    cos0
    syl6reqr
    3ad2ant1
    3eqtrd
    3exp
    adantl
    rexlimdv
    mpd
    @0
    @1
    wn
    #
    wa
    #
    c2
    @9
    cmul
    co
    #
    c1
    caddc
    co
    #
    cK
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    @0
    @40
    @45
    vn
    cK
    odd2np1
    biimpa
    @41
    @44
    @7
    vn
    cz
    @41
    @13
    @44
    w3a
    @4
    @2
    @16
    caddc
    co
    #
    ccos
    cfv
    #
    @2
    ccos
    cfv
    #
    @6
    @0
    @13
    @44
    @4
    @47
    wceq
    @40
    @0
    @13
    @44
    w3a
    @3
    @46
    ccos
    @13
    @44
    @3
    @46
    wceq
    @0
    @13
    @44
    wa
    @3
    @43
    @2
    cmul
    co
    #
    @42
    @2
    cmul
    co
    #
    c1
    @2
    cmul
    co
    #
    caddc
    co
    #
    @46
    @44
    @3
    @49
    wceq
    @13
    @44
    @49
    @3
    @43
    cK
    @2
    cmul
    oveq1
    eqcomd
    adantl
    @13
    @49
    @52
    wceq
    #
    @44
    @13
    @25
    @53
    @26
    @25
    @42
    c1
    @2
    @25
    c2
    @9
    @31
    @35
    mulcld
    #
    @25
    1cnd
    @2
    cc
    wcel
    #
    @25
    negpicn
    a1i
    #
    adddird
    syl
    adantr
    @13
    @52
    @46
    wceq
    #
    @44
    @13
    @25
    @57
    @26
    @25
    @52
    @16
    @2
    caddc
    co
    @46
    @25
    @50
    @16
    @51
    @2
    caddc
    @25
    @50
    @42
    cneg
    #
    cpi
    cmul
    co
    #
    @28
    @16
    @25
    @59
    @50
    @25
    @42
    cc
    wcel
    @32
    @59
    @50
    wceq
    @54
    @33
    @42
    cpi
    mulneg12
    syl2anc
    eqcomd
    @25
    @58
    @27
    cpi
    cmul
    @25
    c2
    @14
    cmul
    co
    @58
    @27
    @25
    c2
    @9
    @31
    @35
    mulneg2d
    @25
    c2
    @14
    @31
    @29
    mulcomd
    eqtr3d
    oveq1d
    @34
    3eqtrd
    @25
    @2
    @56
    mulid2d
    oveq12d
    @25
    @16
    @2
    @30
    @56
    addcomd
    eqtrd
    syl
    adantr
    3eqtrd
    3adant1
    fveq2d
    3adant1r
    @13
    @41
    @47
    @48
    wceq
    #
    @44
    @13
    @55
    @38
    @60
    negpicn
    @39
    @2
    @14
    cosper
    sylancr
    3ad2ant2
    @41
    @13
    @48
    @6
    wceq
    #
    @44
    @40
    @61
    @0
    @40
    @6
    @5
    @48
    @1
    c1
    @5
    iffalse
    cosnegpi
    syl6reqr
    adantl
    3ad2ant1
    3eqtrd
    rexlimdv3a
    mpd
    pm2.61dan
end
