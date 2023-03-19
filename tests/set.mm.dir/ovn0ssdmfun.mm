include "cv.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cfv.mm"
include "cxp.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "neeq1d.mm"
include "ralxp.mm"
include "fvn0ssdmfun.mm"
include "sylbir.mm"

theorem ovn0ssdmfun
  let cD: class D
  let cE: class E
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint D a
  disjoint D b
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint F a
  disjoint F b
  disjoint D p
  disjoint a p
  disjoint b p
  disjoint E p
  disjoint F p
  disjoint k x
  assert |- ( A. a e. D A. b e. E ( a F b ) =/= (/) -> ( ( D X. E ) C_ dom F /\ Fun ( F |` ( D X. E ) ) ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    cF
    co
    #
    c0
    wne
    #
    vb
    cE
    wral
    va
    cD
    wral
    vp
    cv
    #
    cF
    cfv
    #
    c0
    wne
    #
    vp
    cD
    cE
    cxp
    #
    wral
    @7
    cF
    cdm
    wss
    cF
    @7
    cres
    wfun
    wa
    @6
    @3
    vp
    va
    vb
    cD
    cE
    @4
    @0
    @1
    cop
    #
    wceq
    #
    @5
    @2
    c0
    @9
    @5
    @8
    cF
    cfv
    @2
    @4
    @8
    cF
    fveq2
    @0
    @1
    cF
    df-ov
    syl6eqr
    neeq1d
    ralxp
    @7
    cF
    vp
    fvn0ssdmfun
    sylbir
end
