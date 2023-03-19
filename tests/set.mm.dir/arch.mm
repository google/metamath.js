include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "cr.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "wo.mm"
include "wral.mm"
include "wn.mm"
include "nnunb.mm"
include "ralnex.mm"
include "mpbir.mm"
include "wcel.mm"
include "rexnal.mm"
include "wa.mm"
include "wb.mm"
include "nnre.mm"
include "axlttri.mm"
include "sylan2.mm"
include "equcom.mm"
include "orbi1i.mm"
include "orcom.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6bb.mm"
include "biimprd.mm"
include "reximdva.mm"
include "syl5bir.mm"
include "ralimia.mm"
include "ax-mp.mm"
include "vtoclri.mm"

theorem arch
  let cA: class A
  let vn: setvar n
  let vy: setvar y

  disjoint A n
  disjoint n y
  disjoint A y
  assert |- ( A e. RR -> E. n e. NN A < n )

  proof
    vy
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    cA
    @1
    clt
    wbr
    #
    vn
    cn
    wrex
    vy
    cA
    cr
    @0
    cA
    wceq
    @2
    @4
    vn
    cn
    @0
    cA
    @1
    clt
    breq1
    rexbidv
    @1
    @0
    clt
    wbr
    #
    @1
    @0
    wceq
    #
    wo
    #
    vn
    cn
    wral
    #
    wn
    #
    vy
    cr
    wral
    #
    @3
    vy
    cr
    wral
    @10
    @8
    vy
    cr
    wrex
    wn
    vy
    vn
    nnunb
    @8
    vy
    cr
    ralnex
    mpbir
    @9
    @3
    vy
    cr
    @9
    @7
    wn
    #
    vn
    cn
    wrex
    @0
    cr
    wcel
    #
    @3
    @7
    vn
    cn
    rexnal
    @12
    @11
    @2
    vn
    cn
    @12
    @1
    cn
    wcel
    #
    wa
    #
    @2
    @11
    @14
    @2
    @0
    @1
    wceq
    #
    @5
    wo
    #
    wn
    #
    @11
    @13
    @12
    @1
    cr
    wcel
    @2
    @17
    wb
    @1
    nnre
    @0
    @1
    axlttri
    sylan2
    @16
    @7
    @16
    @6
    @5
    wo
    @7
    @15
    @6
    @5
    vy
    vn
    equcom
    orbi1i
    @6
    @5
    orcom
    bitri
    notbii
    syl6bb
    biimprd
    reximdva
    syl5bir
    ralimia
    ax-mp
    vtoclri
end
