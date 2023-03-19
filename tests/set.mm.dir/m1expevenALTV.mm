include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "dfeven4.mm"
include "elrab2.mm"
include "oveq2.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "neg1cn.mm"
include "a1i.mm"
include "neg1ne0.mm"
include "2z.mm"
include "id.mm"
include "expmulz.mm"
include "syl22anc.mm"
include "neg1sqe1.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "adantl.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylbi.mm"

theorem m1expevenALTV
  let cN: class N
  let vi: setvar i
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Even -> ( -u 1 ^ N ) = 1 )

  proof
    cN
    ceven
    wcel
    cN
    cz
    wcel
    #
    cN
    c2
    vi
    cv
    #
    cmul
    co
    #
    wceq
    #
    vi
    cz
    wrex
    #
    wa
    c1
    cneg
    #
    cN
    cexp
    co
    #
    c1
    wceq
    #
    vn
    cv
    #
    @2
    wceq
    #
    vi
    cz
    wrex
    @4
    vn
    cN
    cz
    ceven
    @8
    cN
    wceq
    @9
    @3
    vi
    cz
    @8
    cN
    @2
    eqeq1
    rexbidv
    vn
    vi
    dfeven4
    elrab2
    @0
    @4
    @7
    @0
    @3
    @7
    vi
    cz
    @0
    @1
    cz
    wcel
    #
    wa
    #
    @3
    @7
    @3
    @11
    @6
    @5
    @2
    cexp
    co
    #
    c1
    cN
    @2
    @5
    cexp
    oveq2
    @10
    @12
    c1
    wceq
    @0
    @10
    @12
    @5
    c2
    cexp
    co
    #
    @1
    cexp
    co
    #
    c1
    @10
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    c2
    cz
    wcel
    #
    @10
    @12
    @14
    wceq
    @15
    @10
    neg1cn
    a1i
    @16
    @10
    neg1ne0
    a1i
    @17
    @10
    2z
    a1i
    @10
    id
    @5
    c2
    @1
    expmulz
    syl22anc
    @10
    @14
    c1
    @1
    cexp
    co
    c1
    @13
    c1
    @1
    cexp
    neg1sqe1
    oveq1i
    @1
    1exp
    syl5eq
    eqtrd
    adantl
    sylan9eqr
    ex
    rexlimdva
    imp
    sylbi
end
