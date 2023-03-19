include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "negex.mm"
include "prid1.mm"
include "neg1ne0.mm"
include "cc.mm"
include "wss.mm"
include "neg1cn.mm"
include "ax-1cn.mm"
include "prssi.mm"
include "mp2an.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "sseli.mm"
include "mulm1d.mm"
include "negeq.mm"
include "negneg1e1.mm"
include "1ex.mm"
include "prid2.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "syl.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "mulid2d.mm"
include "id.mm"
include "imp.mm"
include "cdiv.mm"
include "oveq2.mm"
include "ax-1ne0.mm"
include "divneg2.mm"
include "mp3an.mm"
include "1div1e1.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "adantr.mm"
include "expcl2lem.mm"
include "mp3an12.mm"

theorem m1expcl2
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( N e. ZZ -> ( -u 1 ^ N ) e. { -u 1 , 1 } )

  proof
    c1
    cneg
    #
    @0
    c1
    cpr
    #
    wcel
    @0
    cc0
    wne
    cN
    cz
    wcel
    @0
    cN
    cexp
    co
    @1
    wcel
    @0
    c1
    c1
    negex
    prid1
    #
    neg1ne0
    vx
    vy
    @0
    cN
    @1
    @0
    cc
    wcel
    c1
    cc
    wcel
    #
    @1
    cc
    wss
    neg1cn
    ax-1cn
    @0
    c1
    cc
    prssi
    mp2an
    #
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    @5
    @7
    cmul
    co
    #
    @1
    wcel
    #
    @6
    @5
    @0
    wceq
    #
    @5
    c1
    wceq
    #
    wo
    #
    @8
    @10
    wi
    #
    @5
    @0
    c1
    elpri
    #
    @11
    @14
    @12
    @8
    @10
    @11
    @0
    @7
    cmul
    co
    #
    @1
    wcel
    @8
    @16
    @7
    cneg
    #
    @1
    @8
    @7
    @1
    cc
    @7
    @4
    sseli
    #
    mulm1d
    @8
    @7
    @0
    wceq
    #
    @7
    c1
    wceq
    #
    wo
    @17
    @1
    wcel
    #
    @7
    @0
    c1
    elpri
    @19
    @21
    @20
    @19
    @17
    @0
    cneg
    #
    @1
    @7
    @0
    negeq
    @22
    c1
    @1
    negneg1e1
    @0
    c1
    1ex
    prid2
    #
    eqeltri
    syl6eqel
    @20
    @17
    @0
    @1
    @7
    c1
    negeq
    @2
    syl6eqel
    jaoi
    syl
    eqeltrd
    @11
    @9
    @16
    @1
    @5
    @0
    @7
    cmul
    oveq1
    eleq1d
    syl5ibr
    @8
    @10
    @12
    c1
    @7
    cmul
    co
    #
    @1
    wcel
    @8
    @24
    @7
    @1
    @8
    @7
    @18
    mulid2d
    @8
    id
    eqeltrd
    @12
    @9
    @24
    @1
    @5
    c1
    @7
    cmul
    oveq1
    eleq1d
    syl5ibr
    jaoi
    syl
    imp
    @23
    @6
    c1
    @5
    cdiv
    co
    #
    @1
    wcel
    #
    @5
    cc0
    wne
    @6
    @13
    @26
    @15
    @11
    @26
    @12
    @11
    @25
    c1
    @0
    cdiv
    co
    #
    @1
    @5
    @0
    c1
    cdiv
    oveq2
    @27
    @0
    @1
    c1
    c1
    cdiv
    co
    #
    cneg
    #
    @27
    @0
    @3
    @3
    c1
    cc0
    wne
    @29
    @27
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @28
    c1
    1div1e1
    negeqi
    eqtr3i
    @2
    eqeltri
    syl6eqel
    @12
    @25
    @28
    @1
    @5
    c1
    c1
    cdiv
    oveq2
    @28
    c1
    @1
    1div1e1
    @23
    eqeltri
    syl6eqel
    jaoi
    syl
    adantr
    expcl2lem
    mp3an12
end
