include "cxr.mm"
include "wcel.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "id.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "wa.mm"
include "sgn0.mm"
include "a1i.mm"
include "clt.mm"
include "wbr.mm"
include "sgn1.mm"
include "neg1rr.mm"
include "rexri.mm"
include "neg1lt0.mm"
include "sgnn.mm"
include "mp2an.mm"
include "sgn3da.mm"

theorem sgnsgn
  let cA: class A


  assert |- ( A e. RR* -> ( sgn ` ( sgn ` A ) ) = ( sgn ` A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    csgn
    cfv
    #
    csgn
    cfv
    #
    @1
    wceq
    cc0
    csgn
    cfv
    #
    cc0
    wceq
    #
    c1
    csgn
    cfv
    #
    c1
    wceq
    #
    c1
    cneg
    #
    csgn
    cfv
    #
    @7
    wceq
    #
    cA
    @0
    id
    @1
    cc0
    wceq
    #
    @2
    @3
    @1
    cc0
    @1
    cc0
    csgn
    fveq2
    @10
    id
    eqeq12d
    @1
    c1
    wceq
    #
    @2
    @5
    @1
    c1
    @1
    c1
    csgn
    fveq2
    @11
    id
    eqeq12d
    @1
    @7
    wceq
    #
    @2
    @8
    @1
    @7
    @1
    @7
    csgn
    fveq2
    @12
    id
    eqeq12d
    @4
    @0
    cA
    cc0
    wceq
    wa
    sgn0
    a1i
    @6
    @0
    cc0
    cA
    clt
    wbr
    wa
    sgn1
    a1i
    @9
    @0
    cA
    cc0
    clt
    wbr
    wa
    @7
    cxr
    wcel
    @7
    cc0
    clt
    wbr
    @9
    @7
    neg1rr
    rexri
    neg1lt0
    @7
    sgnn
    mp2an
    a1i
    sgn3da
end
