include "c0.mm"
include "wf.mm"
include "wceq.mm"
include "wfn.mm"
include "ffn.mm"
include "fn0.mm"
include "sylib.mm"
include "f0.mm"
include "feq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem f0bi
  let cF: class F
  let cX: class X


  assert |- ( F : (/) --> X <-> F = (/) )

  proof
    c0
    cX
    cF
    wf
    #
    cF
    c0
    wceq
    #
    @0
    cF
    c0
    wfn
    @1
    c0
    cX
    cF
    ffn
    cF
    fn0
    sylib
    @1
    @0
    c0
    cX
    c0
    wf
    cX
    f0
    c0
    cX
    cF
    c0
    feq1
    mpbiri
    impbii
end
