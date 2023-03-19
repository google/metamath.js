include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "df-isom.mm"
include "nff1o.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nffv.mm"
include "nfbi.mm"
include "nfral.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nfiso
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vy: setvar y
  let vz: setvar z
  assume nfiso.1: |- F/_ x H
  assume nfiso.2: |- F/_ x R
  assume nfiso.3: |- F/_ x S
  assume nfiso.4: |- F/_ x A
  assume nfiso.5: |- F/_ x B


  assert |- F/ x H Isom R , S ( A , B )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cH
    wf1o
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    wa
    vx
    vy
    vz
    cA
    cB
    cR
    cS
    cH
    df-isom
    @0
    @9
    vx
    vx
    cA
    cB
    cH
    nfiso.1
    nfiso.4
    nfiso.5
    nff1o
    @8
    vx
    vy
    cA
    nfiso.4
    @7
    vx
    vz
    cA
    nfiso.4
    @3
    @6
    vx
    vx
    @1
    @2
    cR
    vx
    @1
    nfcv
    #
    nfiso.2
    vx
    @2
    nfcv
    #
    nfbr
    vx
    @4
    @5
    cS
    vx
    @1
    cH
    nfiso.1
    @10
    nffv
    nfiso.3
    vx
    @2
    cH
    nfiso.1
    @11
    nffv
    nfbr
    nfbi
    nfral
    nfral
    nfan
    nfxfr
end
