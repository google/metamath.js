include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "fncvm.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "simprd.mm"

theorem cvmtop2
  let cC: class C
  let cF: class F
  let cJ: class J
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x


  assert |- ( F e. ( C CovMap J ) -> J e. Top )

  proof
    cF
    cC
    cJ
    ccvm
    co
    #
    wcel
    #
    cC
    ctop
    wcel
    #
    cJ
    ctop
    wcel
    #
    @1
    @0
    c0
    wceq
    @2
    @3
    wa
    @0
    cF
    n0i
    cC
    cJ
    ctop
    ccvm
    ccvm
    ctop
    ctop
    cxp
    #
    wfn
    ccvm
    cdm
    @4
    wceq
    fncvm
    @4
    ccvm
    fndm
    ax-mp
    ndmov
    nsyl2
    simprd
end
