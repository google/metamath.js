include "cxr.mm"
include "wcel.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "id.mm"
include "eqeq1.mm"
include "imbi1d.mm"
include "wa.mm"
include "neg1ne0.mm"
include "nesymi.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "neg1rr.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "lttri.mm"
include "mp2an.mm"
include "gtneii.mm"
include "neii.mm"
include "simp2.mm"
include "3expia.mm"
include "sgn3da.mm"
include "imp.mm"
include "sgnn.mm"
include "impbida.mm"

theorem sgnnbi
  let cA: class A


  assert |- ( A e. RR* -> ( ( sgn ` A ) = -u 1 <-> A < 0 ) )

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
    cneg
    #
    wceq
    #
    cA
    cc0
    clt
    wbr
    #
    @0
    @3
    @4
    @0
    @3
    @4
    wi
    cc0
    @2
    wceq
    #
    @4
    wi
    #
    c1
    @2
    wceq
    #
    @4
    wi
    #
    @2
    @2
    wceq
    #
    @4
    wi
    cA
    @0
    id
    @1
    cc0
    wceq
    @3
    @5
    @4
    @1
    cc0
    @2
    eqeq1
    imbi1d
    @1
    c1
    wceq
    @3
    @7
    @4
    @1
    c1
    @2
    eqeq1
    imbi1d
    @3
    @3
    @9
    @4
    @1
    @2
    @2
    eqeq1
    imbi1d
    @6
    @0
    cA
    cc0
    wceq
    wa
    @5
    @4
    @2
    cc0
    neg1ne0
    nesymi
    pm2.21i
    a1i
    @8
    @0
    cc0
    cA
    clt
    wbr
    wa
    @7
    @4
    c1
    @2
    @2
    c1
    neg1rr
    @2
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @2
    c1
    clt
    wbr
    neg1lt0
    0lt1
    @2
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    gtneii
    neii
    pm2.21i
    a1i
    @0
    @4
    @9
    @4
    @0
    @4
    @9
    simp2
    3expia
    sgn3da
    imp
    cA
    sgnn
    impbida
end
