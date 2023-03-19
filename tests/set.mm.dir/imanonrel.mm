include "ccnv.mm"
include "cdif.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "c0.mm"
include "df-ima.mm"
include "resnonrel.mm"
include "rneqi.mm"
include "rn0.mm"
include "3eqtri.mm"

theorem imanonrel
  let cA: class A
  let cB: class B


  assert |- ( ( A \ `' `' A ) " B ) = (/)

  proof
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cB
    cima
    @0
    cB
    cres
    #
    crn
    c0
    crn
    c0
    @0
    cB
    df-ima
    @1
    c0
    cA
    cB
    resnonrel
    rneqi
    rn0
    3eqtri
end
