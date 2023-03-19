include "cxp.mm"
include "cvv.mm"
include "wf.mm"
include "ctpos.mm"
include "wfn.mm"
include "tposf.mm"
include "dffn2.mm"
include "3imtr4i.mm"

theorem tposfn
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( F Fn ( A X. B ) -> tpos F Fn ( B X. A ) )

  proof
    cA
    cB
    cxp
    #
    cvv
    cF
    wf
    cB
    cA
    cxp
    #
    cvv
    cF
    ctpos
    #
    wf
    cF
    @0
    wfn
    @2
    @1
    wfn
    cA
    cB
    cvv
    cF
    tposf
    @0
    cF
    dffn2
    @1
    @2
    dffn2
    3imtr4i
end
