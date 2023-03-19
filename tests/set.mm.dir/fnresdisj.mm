include "cres.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wfn.mm"
include "cin.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "ax-mp.mm"
include "dmres.mm"
include "incom.mm"
include "eqtri.mm"
include "fndm.mm"
include "ineq1d.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "syl5rbb.mm"

theorem fnresdisj
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn A -> ( ( A i^i B ) = (/) <-> ( F |` B ) = (/) ) )

  proof
    cF
    cB
    cres
    #
    c0
    wceq
    #
    @0
    cdm
    #
    c0
    wceq
    #
    cF
    cA
    wfn
    #
    cA
    cB
    cin
    #
    c0
    wceq
    @0
    wrel
    @1
    @3
    wb
    cF
    cB
    relres
    @0
    reldm0
    ax-mp
    @4
    @2
    @5
    c0
    @4
    @2
    cF
    cdm
    #
    cB
    cin
    #
    @5
    @2
    cB
    @6
    cin
    @7
    cF
    cB
    dmres
    cB
    @6
    incom
    eqtri
    @4
    @6
    cA
    cB
    cA
    cF
    fndm
    ineq1d
    syl5eq
    eqeq1d
    syl5rbb
end
