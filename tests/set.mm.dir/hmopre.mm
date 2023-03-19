include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "wceq.mm"
include "hmop.mm"
include "3anidm23.mm"
include "eqcomd.mm"
include "wb.mm"
include "hmopf.mm"
include "ffvelrnda.mm"
include "hire.mm"
include "sylancom.mm"
include "mpbird.mm"

theorem hmopre
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T e. HrmOp /\ A e. ~H ) -> ( ( T ` A ) .ih A ) e. RR )

  proof
    cT
    cho
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cT
    cfv
    #
    cA
    csp
    co
    #
    cr
    wcel
    #
    @4
    cA
    @3
    csp
    co
    #
    wceq
    #
    @2
    @6
    @4
    @0
    @1
    @6
    @4
    wceq
    cA
    cA
    cT
    hmop
    3anidm23
    eqcomd
    @0
    @1
    @3
    chil
    wcel
    @5
    @7
    wb
    @0
    chil
    chil
    cA
    cT
    cT
    hmopf
    ffvelrnda
    @3
    cA
    hire
    sylancom
    mpbird
end
