include "ccnfld.mm"
include "cplusf.mm"
include "cfv.mm"
include "caddc.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "ax-addf.mm"
include "ffn.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "plusfeq.mm"
include "mp2b.mm"
include "eqcomi.mm"

theorem cnfldplusf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- + = ( +f ` CCfld )

  proof
    ccnfld
    cplusf
    cfv
    #
    caddc
    cc
    cc
    cxp
    #
    cc
    caddc
    wf
    caddc
    @1
    wfn
    @0
    caddc
    wceq
    ax-addf
    @1
    cc
    caddc
    ffn
    cc
    caddc
    @0
    ccnfld
    cnfldbas
    cnfldadd
    @0
    eqid
    plusfeq
    mp2b
    eqcomi
end
