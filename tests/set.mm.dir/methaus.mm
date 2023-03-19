include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cmopn.mm"
include "wceq.mm"
include "cme.mm"
include "wrex.mm"
include "cha.mm"
include "mopnex.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "w3a.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cbl.mm"
include "cxr.mm"
include "metxmet.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "cr.mm"
include "metcl.mm"
include "3expb.mm"
include "adantr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "metgt0.mm"
include "biimpa.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "rpxrd.mm"
include "eqid.mm"
include "blopn.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "crp.mm"
include "blcntr.mm"
include "cxad.mm"
include "cle.mm"
include "caddc.mm"
include "rpred.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2halvesd.mm"
include "eqtrd.mm"
include "leidd.mm"
include "eqbrtrd.mm"
include "bldisj.mm"
include "syl33anc.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "ex.mm"
include "ralrimivva.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "ishaus2.mm"
include "3syl.mm"
include "mpbird.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "syl.mm"

theorem methaus
  let cD: class D
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cA: class A
  assume methaus.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. Haus )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    cJ
    vd
    cv
    #
    cmopn
    cfv
    #
    wceq
    #
    vd
    cX
    cme
    cfv
    #
    wrex
    cJ
    cha
    wcel
    #
    cD
    cJ
    cX
    vd
    methaus.1
    mopnex
    @3
    @5
    vd
    @4
    @1
    @4
    wcel
    #
    @5
    @3
    @2
    cha
    wcel
    #
    @6
    @7
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @8
    vm
    cv
    #
    wcel
    #
    @9
    vn
    cv
    #
    wcel
    #
    @11
    @13
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    @2
    wrex
    vm
    @2
    wrex
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @6
    @19
    vx
    vy
    cX
    cX
    @6
    @8
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    #
    wa
    #
    @10
    @18
    @24
    @10
    wa
    #
    @8
    @8
    @9
    @1
    co
    #
    c2
    cdiv
    co
    #
    @1
    cbl
    cfv
    #
    co
    #
    @2
    wcel
    #
    @9
    @27
    @28
    co
    #
    @2
    wcel
    #
    @8
    @29
    wcel
    #
    @9
    @31
    wcel
    #
    @29
    @31
    cin
    #
    c0
    wceq
    #
    @18
    @25
    @1
    @0
    wcel
    #
    @21
    @27
    cxr
    wcel
    #
    @30
    @6
    @37
    @23
    @10
    @1
    cX
    metxmet
    #
    ad2antrr
    #
    @6
    @21
    @22
    @10
    simplrl
    #
    @25
    @27
    @25
    @26
    @25
    @26
    @24
    @26
    cr
    wcel
    #
    @10
    @6
    @21
    @22
    @42
    @8
    @9
    @1
    cX
    metcl
    3expb
    adantr
    #
    @24
    @10
    cc0
    @26
    clt
    wbr
    #
    @6
    @21
    @22
    @10
    @44
    wb
    @8
    @9
    @1
    cX
    metgt0
    3expb
    biimpa
    elrpd
    rphalfcld
    #
    rpxrd
    #
    @1
    @8
    @27
    @2
    cX
    @2
    eqid
    #
    blopn
    syl3anc
    @25
    @37
    @22
    @38
    @32
    @40
    @6
    @21
    @22
    @10
    simplrr
    #
    @46
    @1
    @9
    @27
    @2
    cX
    @47
    blopn
    syl3anc
    @25
    @37
    @21
    @27
    crp
    wcel
    #
    @33
    @40
    @41
    @45
    @1
    @8
    @27
    cX
    blcntr
    syl3anc
    @25
    @37
    @22
    @49
    @34
    @40
    @48
    @45
    @1
    @9
    @27
    cX
    blcntr
    syl3anc
    @25
    @37
    @21
    @22
    @38
    @38
    @27
    @27
    cxad
    co
    #
    @26
    cle
    wbr
    @36
    @40
    @41
    @48
    @46
    @46
    @25
    @50
    @26
    @26
    cle
    @25
    @50
    @27
    @27
    caddc
    co
    #
    @26
    @25
    @27
    cr
    wcel
    #
    @52
    @50
    @51
    wceq
    @25
    @27
    @45
    rpred
    #
    @53
    @27
    @27
    rexadd
    syl2anc
    @25
    @26
    @25
    @26
    @43
    recnd
    2halvesd
    eqtrd
    @25
    @26
    @43
    leidd
    eqbrtrd
    @1
    @8
    @9
    @27
    @27
    cX
    bldisj
    syl33anc
    @17
    @33
    @34
    @36
    w3a
    @33
    @14
    @29
    @13
    cin
    #
    c0
    wceq
    #
    w3a
    vm
    vn
    @29
    @31
    @2
    @2
    @11
    @29
    wceq
    #
    @12
    @33
    @16
    @55
    @14
    @11
    @29
    @8
    eleq2
    @56
    @15
    @54
    c0
    @11
    @29
    @13
    ineq1
    eqeq1d
    3anbi13d
    @13
    @31
    wceq
    #
    @14
    @34
    @55
    @36
    @33
    @13
    @31
    @9
    eleq2
    @57
    @54
    @35
    c0
    @13
    @31
    @29
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    ex
    ralrimivva
    @6
    @37
    @2
    cX
    ctopon
    cfv
    wcel
    @7
    @20
    wb
    @39
    @1
    @2
    cX
    @47
    mopntopon
    vx
    vy
    vn
    vm
    @2
    cX
    ishaus2
    3syl
    mpbird
    cJ
    @2
    cha
    eleq1
    syl5ibrcom
    rexlimiv
    syl
end
