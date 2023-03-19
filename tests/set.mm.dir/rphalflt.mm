include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "elrp.mm"
include "halfpos.mm"
include "biimpa.mm"
include "sylbi.mm"

theorem rphalflt
  let cA: class A


  assert |- ( A e. RR+ -> ( A / 2 ) < A )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    cA
    c2
    cdiv
    co
    cA
    clt
    wbr
    #
    cA
    elrp
    @0
    @1
    @2
    cA
    halfpos
    biimpa
    sylbi
end
