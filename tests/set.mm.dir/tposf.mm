include "cxp.mm"
include "wf.mm"
include "ccnv.mm"
include "ctpos.mm"
include "wrel.mm"
include "wi.mm"
include "relxp.mm"
include "tposf2.mm"
include "ax-mp.mm"
include "cnvxp.mm"
include "feq2i.mm"
include "sylib.mm"

theorem tposf
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( F : ( A X. B ) --> C -> tpos F : ( B X. A ) --> C )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wf
    #
    @0
    ccnv
    #
    cC
    cF
    ctpos
    #
    wf
    #
    cB
    cA
    cxp
    #
    cC
    @3
    wf
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
    tposf2
    ax-mp
    @2
    @5
    cC
    @3
    cA
    cB
    cnvxp
    feq2i
    sylib
end
