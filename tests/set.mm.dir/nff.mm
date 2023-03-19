include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "df-f.mm"
include "nffn.mm"
include "nfrn.mm"
include "nfss.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nff
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nff.1: |- F/_ x F
  assume nff.2: |- F/_ x A
  assume nff.3: |- F/_ x B


  assert |- F/ x F : A --> B

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    vx
    cA
    cB
    cF
    df-f
    @0
    @2
    vx
    vx
    cA
    cF
    nff.1
    nff.2
    nffn
    vx
    @1
    cB
    vx
    cF
    nff.1
    nfrn
    nff.3
    nfss
    nfan
    nfxfr
end
