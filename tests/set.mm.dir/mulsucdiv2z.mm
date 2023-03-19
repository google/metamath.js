include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "cmul.mm"
include "zeo.mm"
include "wi.mm"
include "wa.mm"
include "peano2z.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "wb.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "zcn.mm"
include "zcnd.mm"
include "2cnne0.mm"
include "a1i.mm"
include "div23.mm"
include "syl3anc.mm"
include "eleq1d.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "ancoms.mm"
include "divass.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem mulsucdiv2z
  let cN: class N


  assert |- ( N e. ZZ -> ( ( N x. ( N + 1 ) ) / 2 ) e. ZZ )

  proof
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
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
    wo
    cN
    cz
    wcel
    #
    cN
    @2
    cmul
    co
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    zeo
    @1
    @5
    @7
    wi
    @4
    @1
    @5
    @7
    @1
    @5
    wa
    @7
    @0
    @2
    cmul
    co
    #
    cz
    wcel
    #
    @5
    @1
    @2
    cz
    wcel
    @9
    cN
    peano2z
    #
    @0
    @2
    zmulcl
    sylan2
    @5
    @7
    @9
    wb
    @1
    @5
    @6
    @8
    cz
    @5
    cN
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @6
    @8
    wceq
    cN
    zcn
    #
    @5
    @2
    @10
    zcnd
    #
    @13
    @5
    2cnne0
    a1i
    #
    cN
    @2
    c2
    div23
    syl3anc
    eleq1d
    adantl
    mpbird
    ex
    @4
    @5
    @7
    @4
    @5
    wa
    @7
    cN
    @3
    cmul
    co
    #
    cz
    wcel
    #
    @5
    @4
    @18
    cN
    @3
    zmulcl
    ancoms
    @5
    @7
    @18
    wb
    @4
    @5
    @6
    @17
    cz
    @5
    @11
    @12
    @13
    @6
    @17
    wceq
    @14
    @15
    @16
    cN
    @2
    c2
    divass
    syl3anc
    eleq1d
    adantl
    mpbird
    ex
    jaoi
    mpcom
end
