include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "2z.mm"
include "divides.mm"
include "mpan.mm"
include "biimpa.mm"
include "wi.mm"
include "w3a.mm"
include "zcn.mm"
include "2cnd.mm"
include "cc.mm"
include "picn.mm"
include "a1i.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "adantr.mm"
include "oveq1.mm"
include "adantl.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "cos2kpi.mm"
include "eqtrd.mm"
include "3adant1.mm"
include "iftrue.mm"
include "3ad2ant1.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "wn.mm"
include "caddc.mm"
include "odd2np1.mm"
include "mulcld.mm"
include "1cnd.mm"
include "adddird.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "mulid2i.mm"
include "oveq12d.mm"
include "2cn.mm"
include "mulcli.mm"
include "addcomd.mm"
include "3eqtrrd.mm"
include "cosper.mm"
include "cospi.mm"
include "3eqtrd.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem coskpi2
  let cK: class K
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( K e. ZZ -> ( cos ` ( K x. _pi ) ) = if ( 2 || K , 1 , -u 1 ) )

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
    @6
    @0
    @1
    @11
    c2
    cz
    wcel
    @0
    @1
    @11
    wb
    2z
    vn
    c2
    cK
    divides
    mpan
    biimpa
    @7
    @10
    @6
    vn
    cz
    @1
    @8
    cz
    wcel
    #
    @10
    @6
    wi
    wi
    @0
    @1
    @12
    @10
    @6
    @1
    @12
    @10
    w3a
    @3
    c1
    @5
    @12
    @10
    @3
    c1
    wceq
    @1
    @12
    @10
    wa
    #
    @3
    @8
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    ccos
    cfv
    #
    c1
    @13
    @2
    @15
    ccos
    @13
    @15
    @9
    cpi
    cmul
    co
    #
    @2
    @12
    @15
    @17
    wceq
    @10
    @12
    @17
    @15
    @12
    @8
    c2
    cpi
    @8
    zcn
    #
    @12
    2cnd
    #
    cpi
    cc
    wcel
    #
    @12
    picn
    a1i
    #
    mulassd
    #
    eqcomd
    adantr
    @10
    @17
    @2
    wceq
    @12
    @9
    cK
    cpi
    cmul
    oveq1
    adantl
    eqtr2d
    fveq2d
    @12
    @16
    c1
    wceq
    @10
    @8
    cos2kpi
    adantr
    eqtrd
    3adant1
    @1
    @12
    c1
    @5
    wceq
    @10
    @1
    @5
    c1
    @1
    c1
    @4
    iftrue
    eqcomd
    3ad2ant1
    eqtrd
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
    @8
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
    @6
    @0
    @23
    @28
    vn
    cK
    odd2np1
    biimpa
    @24
    @27
    @6
    vn
    cz
    @23
    @12
    @27
    @6
    wi
    wi
    @0
    @23
    @12
    @27
    @6
    @23
    @12
    @27
    w3a
    @3
    @4
    @5
    @12
    @27
    @3
    @4
    wceq
    @23
    @12
    @27
    wa
    #
    @3
    cpi
    @15
    caddc
    co
    #
    ccos
    cfv
    #
    cpi
    ccos
    cfv
    #
    @4
    @29
    @2
    @30
    ccos
    @29
    @30
    @26
    cpi
    cmul
    co
    #
    @2
    @12
    @30
    @33
    wceq
    @27
    @12
    @33
    @25
    cpi
    cmul
    co
    #
    c1
    cpi
    cmul
    co
    #
    caddc
    co
    @15
    cpi
    caddc
    co
    @30
    @12
    @25
    c1
    cpi
    @12
    c2
    @8
    @19
    @18
    mulcld
    @12
    1cnd
    @21
    adddird
    @12
    @34
    @15
    @35
    cpi
    caddc
    @12
    @34
    @17
    @15
    @12
    @25
    @9
    cpi
    cmul
    @12
    c2
    @8
    @19
    @18
    mulcomd
    oveq1d
    @22
    eqtrd
    @35
    cpi
    wceq
    @12
    cpi
    picn
    mulid2i
    a1i
    oveq12d
    @12
    @15
    cpi
    @12
    @8
    @14
    @18
    @14
    cc
    wcel
    @12
    c2
    cpi
    2cn
    picn
    mulcli
    a1i
    mulcld
    @21
    addcomd
    3eqtrrd
    adantr
    @27
    @33
    @2
    wceq
    @12
    @26
    cK
    cpi
    cmul
    oveq1
    adantl
    eqtr2d
    fveq2d
    @12
    @31
    @32
    wceq
    #
    @27
    @20
    @12
    @36
    picn
    cpi
    @8
    cosper
    mpan
    adantr
    @32
    @4
    wceq
    @29
    cospi
    a1i
    3eqtrd
    3adant1
    @23
    @12
    @4
    @5
    wceq
    @27
    @23
    @5
    @4
    @1
    c1
    @4
    iffalse
    eqcomd
    3ad2ant1
    eqtrd
    3exp
    adantl
    rexlimdv
    mpd
    pm2.61dan
end
