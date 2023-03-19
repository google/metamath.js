include "cxr.mm"
include "wcel.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "cneg.mm"
include "id.mm"
include "eqeq1.mm"
include "imbi1d.mm"
include "wa.mm"
include "0ne1.mm"
include "neii.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "simp2.mm"
include "3expia.mm"
include "neg1rr.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "lttri.mm"
include "mp2an.mm"
include "gtneii.mm"
include "nesymi.mm"
include "sgn3da.mm"
include "imp.mm"
include "sgnp.mm"
include "impbida.mm"

theorem sgnpbi
  let cA: class A


  assert |- ( A e. RR* -> ( ( sgn ` A ) = 1 <-> 0 < A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    csgn
    cfv
    #
    c1
    wceq
    #
    cc0
    cA
    clt
    wbr
    #
    @0
    @2
    @3
    @0
    @2
    @3
    wi
    cc0
    c1
    wceq
    #
    @3
    wi
    #
    c1
    c1
    wceq
    #
    @3
    wi
    c1
    cneg
    #
    c1
    wceq
    #
    @3
    wi
    #
    cA
    @0
    id
    @1
    cc0
    wceq
    @2
    @4
    @3
    @1
    cc0
    c1
    eqeq1
    imbi1d
    @2
    @2
    @6
    @3
    @1
    c1
    c1
    eqeq1
    imbi1d
    @1
    @7
    wceq
    @2
    @8
    @3
    @1
    @7
    c1
    eqeq1
    imbi1d
    @5
    @0
    cA
    cc0
    wceq
    wa
    @4
    @3
    cc0
    c1
    0ne1
    neii
    pm2.21i
    a1i
    @0
    @3
    @6
    @3
    @0
    @3
    @6
    simp2
    3expia
    @9
    @0
    cA
    cc0
    clt
    wbr
    wa
    @8
    @3
    c1
    @7
    @7
    c1
    neg1rr
    @7
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @7
    c1
    clt
    wbr
    neg1lt0
    0lt1
    @7
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    gtneii
    nesymi
    pm2.21i
    a1i
    sgn3da
    imp
    cA
    sgnp
    impbida
end
