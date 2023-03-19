include "cxp.mm"
include "wfo.mm"
include "ccnv.mm"
include "ctpos.mm"
include "wrel.mm"
include "wi.mm"
include "relxp.mm"
include "tposfo2.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "cnvxp.mm"
include "foeq2.mm"
include "sylib.mm"

theorem tposfo
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( F : ( A X. B ) -onto-> C -> tpos F : ( B X. A ) -onto-> C )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wfo
    #
    @0
    ccnv
    #
    cC
    cF
    ctpos
    #
    wfo
    #
    cB
    cA
    cxp
    #
    cC
    @3
    wfo
    #
    @0
    wrel
    @1
    @4
    wi
    cA
    cB
    relxp
    @0
    cC
    cF
    tposfo2
    ax-mp
    @2
    @5
    wceq
    @4
    @6
    wb
    cA
    cB
    cnvxp
    @2
    @5
    cC
    @3
    foeq2
    ax-mp
    sylib
end
