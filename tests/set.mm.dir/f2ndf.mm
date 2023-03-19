include "wf.mm"
include "c2nd.mm"
include "cres.mm"
include "cxp.mm"
include "wss.mm"
include "f2ndres.mm"
include "fssxp.mm"
include "fssres.mm"
include "sylancr.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem f2ndf
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ( 2nd |` F ) : F --> B )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cB
    c2nd
    cF
    cres
    #
    wf
    cF
    cB
    c2nd
    cA
    cB
    cxp
    #
    cres
    #
    cF
    cres
    #
    wf
    #
    @0
    @2
    cB
    @3
    wf
    cF
    @2
    wss
    @5
    cA
    cB
    f2ndres
    cA
    cB
    cF
    fssxp
    #
    @2
    cB
    cF
    @3
    fssres
    sylancr
    @0
    cF
    cB
    @1
    @4
    @0
    @4
    @1
    @0
    c2nd
    cF
    @2
    @6
    resabs1d
    eqcomd
    feq1d
    mpbird
end
