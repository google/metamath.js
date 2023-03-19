include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cbp.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "bpolyval.mm"
include "mpan.mm"
include "exp0.mm"
include "oveq1d.mm"
include "c0.mm"
include "risefall0lem.mm"
include "sumeq1i.mm"
include "sum0.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem bpoly0
  let cX: class X
  let vk: setvar k


  assert |- ( X e. CC -> ( 0 BernPoly X ) = 1 )

  proof
    cX
    cc
    wcel
    #
    cc0
    cX
    cbp
    co
    #
    cX
    cc0
    cexp
    co
    #
    cc0
    cc0
    c1
    cmin
    co
    cfz
    co
    #
    cc0
    vk
    cv
    #
    cbc
    co
    @4
    cX
    cbp
    co
    cc0
    @4
    cmin
    co
    c1
    caddc
    co
    cdiv
    co
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    c1
    cc0
    cn0
    wcel
    @0
    @1
    @7
    wceq
    0nn0
    vk
    cc0
    cX
    bpolyval
    mpan
    @0
    @7
    c1
    @6
    cmin
    co
    #
    c1
    @0
    @2
    c1
    @6
    cmin
    cX
    exp0
    oveq1d
    @8
    c1
    cc0
    cmin
    co
    c1
    @6
    cc0
    c1
    cmin
    @6
    c0
    @5
    vk
    csu
    cc0
    @3
    c0
    @5
    vk
    risefall0lem
    sumeq1i
    @5
    vk
    sum0
    eqtri
    oveq2i
    1m0e1
    eqtri
    syl6eq
    eqtrd
end
