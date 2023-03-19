include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cbp.mm"
include "co.mm"
include "cexp.mm"
include "cc0.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "c2.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "bpolyval.mm"
include "mpan.mm"
include "exp1.mm"
include "1m1e0.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "cz.mm"
include "0z.mm"
include "bpoly0.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "halfcn.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "syl6eqel.mm"
include "oveq2.mm"
include "bcn0.mm"
include "ax-mp.mm"
include "oveq1.mm"
include "1m0e1.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "fsum1.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem bpoly1
  let cX: class X
  let vk: setvar k


  assert |- ( X e. CC -> ( 1 BernPoly X ) = ( X - ( 1 / 2 ) ) )

  proof
    cX
    cc
    wcel
    #
    c1
    cX
    cbp
    co
    #
    cX
    c1
    cexp
    co
    #
    cc0
    c1
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    vk
    cv
    #
    cbc
    co
    #
    @5
    cX
    cbp
    co
    #
    c1
    @5
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    cX
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    c1
    cn0
    wcel
    #
    @0
    @1
    @13
    wceq
    1nn0
    vk
    c1
    cX
    bpolyval
    mpan
    @0
    @2
    cX
    @12
    @14
    cmin
    cX
    exp1
    @0
    @12
    cc0
    cc0
    cfz
    co
    #
    @11
    vk
    csu
    #
    @14
    @4
    @16
    @11
    vk
    @3
    cc0
    cc0
    cfz
    1m1e0
    oveq2i
    sumeq1i
    @0
    @17
    c1
    cc0
    cX
    cbp
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @14
    @0
    cc0
    cz
    wcel
    @20
    cc
    wcel
    @17
    @20
    wceq
    0z
    @0
    @20
    @14
    cc
    @0
    @20
    c1
    @14
    cmul
    co
    @14
    @0
    @19
    @14
    c1
    cmul
    @0
    @18
    c1
    c2
    cdiv
    cX
    bpoly0
    oveq1d
    oveq2d
    @14
    halfcn
    mulid2i
    syl6eq
    #
    halfcn
    syl6eqel
    @11
    @20
    vk
    cc0
    @5
    cc0
    wceq
    #
    @6
    c1
    @10
    @19
    cmul
    @22
    @6
    c1
    cc0
    cbc
    co
    #
    c1
    @5
    cc0
    c1
    cbc
    oveq2
    @15
    @23
    c1
    wceq
    1nn0
    c1
    bcn0
    ax-mp
    syl6eq
    @22
    @7
    @18
    @9
    c2
    cdiv
    @5
    cc0
    cX
    cbp
    oveq1
    @22
    @9
    c1
    c1
    caddc
    co
    c2
    @22
    @8
    c1
    c1
    caddc
    @22
    @8
    c1
    cc0
    cmin
    co
    c1
    @5
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq1d
    df-2
    syl6eqr
    oveq12d
    oveq12d
    fsum1
    sylancr
    @21
    eqtrd
    syl5eq
    oveq12d
    eqtrd
end
