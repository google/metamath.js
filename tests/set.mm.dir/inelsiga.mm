include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "cdif.mm"
include "dfin4.mm"
include "difelsiga.mm"
include "syld3an3.mm"
include "syl5eqel.mm"

theorem inelsiga
  let cA: class A
  let cB: class B
  let cS: class S


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    cA
    cB
    cin
    cA
    cA
    cB
    cdif
    #
    cdif
    #
    cS
    cA
    cB
    dfin4
    @0
    @1
    @2
    @3
    cS
    wcel
    @4
    cS
    wcel
    cA
    cB
    cS
    difelsiga
    cA
    @3
    cS
    difelsiga
    syld3an3
    syl5eqel
end
