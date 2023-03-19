include "wwe.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "df-we.mm"
include "nffr.mm"
include "nfso.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nfwe
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nffr.r: |- F/_ x R
  assume nffr.a: |- F/_ x A


  assert |- F/ x R We A

  proof
    cA
    cR
    wwe
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    vx
    cA
    cR
    df-we
    @0
    @1
    vx
    vx
    cA
    cR
    nffr.r
    nffr.a
    nffr
    vx
    cA
    cR
    nffr.r
    nffr.a
    nfso
    nfan
    nfxfr
end
