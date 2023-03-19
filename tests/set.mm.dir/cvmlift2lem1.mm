include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "wb.mm"
include "cii.mm"
include "cnei.mm"
include "cfv.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "biimp.mm"
include "ctop.mm"
include "iitop.mm"
include "iiuni.mm"
include "neii1.mm"
include "mpan.mm"
include "adantl.mm"
include "xpss1.mm"
include "syl.mm"
include "simpl.mm"
include "sstrd.mm"
include "ssnei.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "vsnid.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "ssel.mm"
include "syl5com.mm"
include "embantd.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "com12.mm"
include "dfss3.mm"
include "eleq1.mm"
include "ralxp.mm"
include "weq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "ralbii.mm"
include "3bitri.mm"
include "syl6ibr.mm"

theorem cvmlift2lem1
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let cM: class M
  let vz: setvar z

  disjoint t u
  disjoint t x
  disjoint t y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint M u
  disjoint M y
  disjoint t z
  disjoint u z
  disjoint x z
  disjoint y z
  disjoint M z
  assert |- ( A. y e. ( 0 [,] 1 ) E. u e. ( ( nei ` II ) ` { y } ) ( ( u X. { x } ) C_ M <-> ( u X. { t } ) C_ M ) -> ( ( ( 0 [,] 1 ) X. { x } ) C_ M -> ( ( 0 [,] 1 ) X. { t } ) C_ M ) )

  proof
    vu
    cv
    #
    vx
    cv
    csn
    #
    cxp
    #
    cM
    wss
    #
    @0
    vt
    cv
    #
    csn
    #
    cxp
    #
    cM
    wss
    #
    wb
    #
    vu
    vy
    cv
    #
    csn
    #
    cii
    cnei
    cfv
    cfv
    #
    wrex
    #
    vy
    cc0
    c1
    cicc
    co
    #
    wral
    #
    @13
    @1
    cxp
    #
    cM
    wss
    #
    @9
    @4
    cop
    #
    cM
    wcel
    #
    vy
    @13
    wral
    #
    @13
    @5
    cxp
    #
    cM
    wss
    #
    @16
    @14
    @19
    @16
    @12
    @18
    vy
    @13
    @16
    @8
    @18
    vu
    @11
    @8
    @3
    @7
    wi
    @16
    @0
    @11
    wcel
    #
    wa
    #
    @18
    @3
    @7
    biimp
    @23
    @3
    @7
    @18
    @23
    @2
    @15
    cM
    @23
    @0
    @13
    wss
    #
    @2
    @15
    wss
    @22
    @24
    @16
    cii
    ctop
    wcel
    #
    @22
    @24
    iitop
    @10
    cii
    @0
    @13
    iiuni
    neii1
    mpan
    adantl
    @0
    @13
    @1
    xpss1
    syl
    @16
    @22
    simpl
    sstrd
    @23
    @17
    @6
    wcel
    #
    @7
    @18
    @23
    @9
    @0
    wcel
    #
    @4
    @5
    wcel
    @26
    @23
    @10
    @0
    wss
    #
    @27
    @22
    @28
    @16
    @25
    @22
    @28
    iitop
    @10
    cii
    @0
    ssnei
    mpan
    adantl
    @9
    @0
    vy
    vex
    snss
    sylibr
    vt
    vsnid
    @9
    @4
    @0
    @5
    opelxpi
    sylancl
    @6
    cM
    @17
    ssel
    syl5com
    embantd
    syl5
    rexlimdva
    ralimdv
    com12
    @21
    vz
    cv
    #
    cM
    wcel
    #
    vz
    @20
    wral
    @9
    @0
    cop
    #
    cM
    wcel
    #
    vu
    @5
    wral
    #
    vy
    @13
    wral
    @19
    vz
    @20
    cM
    dfss3
    @30
    @32
    vz
    vy
    vu
    @13
    @5
    @29
    @31
    cM
    eleq1
    ralxp
    @33
    @18
    vy
    @13
    @32
    @18
    vu
    @4
    vt
    vex
    vu
    vt
    weq
    @31
    @17
    cM
    @0
    @4
    @9
    opeq2
    eleq1d
    ralsn
    ralbii
    3bitri
    syl6ibr
end
