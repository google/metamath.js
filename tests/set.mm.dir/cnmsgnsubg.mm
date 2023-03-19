include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cc.mm"
include "elpri.mm"
include "id.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "neg1cn.mm"
include "jaoi.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "neg1ne0.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "oveq12.mm"
include "mulid1i.mm"
include "1ex.mm"
include "prid1.mm"
include "eqeltri.mm"
include "negex.mm"
include "prid2.mm"
include "mulid2i.mm"
include "neg1mulneg1e1.mm"
include "ccase.mm"
include "syl2an.mm"
include "cdiv.mm"
include "oveq2.mm"
include "1div1e1.mm"
include "divneg2.mm"
include "mp3an.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "cnmsubglem.mm"

theorem cnmsgnsubg
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume cnmsgnsubg.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )


  assert |- { 1 , -u 1 } e. ( SubGrp ` M )

  proof
    vx
    vy
    c1
    c1
    cneg
    #
    cpr
    #
    cM
    cnmsgnsubg.m
    vx
    cv
    #
    @1
    wcel
    #
    @2
    c1
    wceq
    #
    @2
    @0
    wceq
    #
    wo
    #
    @2
    cc
    wcel
    #
    @2
    c1
    @0
    elpri
    #
    @4
    @7
    @5
    @4
    @2
    c1
    cc
    @4
    id
    #
    ax-1cn
    syl6eqel
    @5
    @2
    @0
    cc
    @5
    id
    #
    neg1cn
    syl6eqel
    jaoi
    syl
    @3
    @6
    @2
    cc0
    wne
    #
    @8
    @4
    @11
    @5
    @4
    @2
    c1
    cc0
    @9
    c1
    cc0
    wne
    #
    @4
    ax-1ne0
    a1i
    eqnetrd
    @5
    @2
    @0
    cc0
    @10
    @0
    cc0
    wne
    @5
    neg1ne0
    a1i
    eqnetrd
    jaoi
    syl
    @3
    @6
    vy
    cv
    #
    c1
    wceq
    #
    @13
    @0
    wceq
    #
    wo
    @2
    @13
    cmul
    co
    #
    @1
    wcel
    #
    @13
    @1
    wcel
    @8
    @13
    c1
    @0
    elpri
    @4
    @14
    @5
    @15
    @17
    @4
    @14
    wa
    @16
    c1
    c1
    cmul
    co
    #
    @1
    @2
    c1
    @13
    c1
    cmul
    oveq12
    @18
    c1
    @1
    c1
    ax-1cn
    mulid1i
    c1
    @0
    1ex
    prid1
    #
    eqeltri
    syl6eqel
    @5
    @14
    wa
    @16
    @0
    c1
    cmul
    co
    #
    @1
    @2
    @0
    @13
    c1
    cmul
    oveq12
    @20
    @0
    @1
    @0
    neg1cn
    mulid1i
    c1
    @0
    c1
    negex
    prid2
    #
    eqeltri
    syl6eqel
    @4
    @15
    wa
    @16
    c1
    @0
    cmul
    co
    #
    @1
    @2
    c1
    @13
    @0
    cmul
    oveq12
    @22
    @0
    @1
    @0
    neg1cn
    mulid2i
    @21
    eqeltri
    syl6eqel
    @5
    @15
    wa
    @16
    @0
    @0
    cmul
    co
    #
    @1
    @2
    @0
    @13
    @0
    cmul
    oveq12
    @23
    c1
    @1
    neg1mulneg1e1
    @19
    eqeltri
    syl6eqel
    ccase
    syl2an
    @19
    @3
    @6
    c1
    @2
    cdiv
    co
    #
    @1
    wcel
    #
    @8
    @4
    @25
    @5
    @4
    @24
    c1
    c1
    cdiv
    co
    #
    @1
    @2
    c1
    c1
    cdiv
    oveq2
    @26
    c1
    @1
    1div1e1
    @19
    eqeltri
    syl6eqel
    @5
    @24
    c1
    @0
    cdiv
    co
    #
    @1
    @2
    @0
    c1
    cdiv
    oveq2
    @27
    @0
    @1
    @26
    cneg
    #
    @27
    @0
    c1
    cc
    wcel
    #
    @29
    @12
    @28
    @27
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @26
    c1
    1div1e1
    negeqi
    eqtr3i
    @21
    eqeltri
    syl6eqel
    jaoi
    syl
    cnmsubglem
end
