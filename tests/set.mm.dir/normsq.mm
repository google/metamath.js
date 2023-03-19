include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csp.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "ifhvhv0.mm"
include "normsqi.mm"
include "dedth.mm"

theorem normsq
  let cA: class A


  assert |- ( A e. ~H -> ( ( normh ` A ) ^ 2 ) = ( A .ih A ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cA
    csp
    co
    #
    wceq
    @0
    cA
    c0v
    cif
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @4
    @4
    csp
    co
    #
    wceq
    cA
    c0v
    cA
    @4
    wceq
    #
    @2
    @6
    @3
    @7
    @8
    @1
    @5
    c2
    cexp
    cA
    @4
    cno
    fveq2
    oveq1d
    @8
    cA
    @4
    cA
    @4
    csp
    @8
    id
    #
    @9
    oveq12d
    eqeq12d
    @4
    cA
    ifhvhv0
    normsqi
    dedth
end
