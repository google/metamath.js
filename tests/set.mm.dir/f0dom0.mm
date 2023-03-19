include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "feq2.mm"
include "f0bi.mm"
include "biimpi.mm"
include "syl6bi.mm"
include "com12.mm"
include "feq1.mm"
include "cdm.mm"
include "dm0.mm"
include "fdm.mm"
include "syl5reqr.mm"
include "impbid.mm"

theorem f0dom0
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( F : X --> Y -> ( X = (/) <-> F = (/) ) )

  proof
    cX
    cY
    cF
    wf
    #
    cX
    c0
    wceq
    #
    cF
    c0
    wceq
    #
    @1
    @0
    @2
    @1
    @0
    c0
    cY
    cF
    wf
    #
    @2
    cX
    c0
    cY
    cF
    feq2
    @3
    @2
    cF
    cY
    f0bi
    biimpi
    syl6bi
    com12
    @2
    @0
    @1
    @2
    @0
    cX
    cY
    c0
    wf
    #
    @1
    cX
    cY
    cF
    c0
    feq1
    @4
    c0
    c0
    cdm
    cX
    dm0
    cX
    cY
    c0
    fdm
    syl5reqr
    syl6bi
    com12
    impbid
end
