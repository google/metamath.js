include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cdm.mm"
include "dmeq.mm"
include "fndm.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "fneq2.mm"
include "biimparc.mm"
include "eqfnfv.mm"
include "sylan2.mm"
include "anassrs.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem eqfnfv2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let wph: wff ph

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  assert |- ( ( F Fn A /\ G Fn B ) -> ( F = G <-> ( A = B /\ A. x e. A ( F ` x ) = ( G ` x ) ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    cF
    cG
    wceq
    #
    cA
    cB
    wceq
    #
    @3
    wa
    @4
    vx
    cv
    #
    cF
    cfv
    @5
    cG
    cfv
    wceq
    vx
    cA
    wral
    #
    wa
    @2
    @3
    @4
    @3
    cF
    cdm
    #
    cG
    cdm
    #
    wceq
    @2
    @4
    cF
    cG
    dmeq
    @0
    @1
    @7
    cA
    @8
    cB
    cA
    cF
    fndm
    cB
    cG
    fndm
    eqeqan12d
    syl5ib
    pm4.71rd
    @2
    @4
    @3
    @6
    @0
    @1
    @4
    @3
    @6
    wb
    #
    @1
    @4
    wa
    @0
    cG
    cA
    wfn
    #
    @9
    @4
    @10
    @1
    cA
    cB
    cG
    fneq2
    biimparc
    vx
    cA
    cF
    cG
    eqfnfv
    sylan2
    anassrs
    pm5.32da
    bitrd
end
