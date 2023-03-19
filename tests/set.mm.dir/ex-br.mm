include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "wcel.mm"
include "wbr.mm"
include "opex.mm"
include "prid2.mm"
include "id.mm"
include "syl5eleqr.mm"
include "df-br.mm"
include "sylibr.mm"

theorem ex-br
  let cR: class R


  assert |- ( R = { <. 2 , 6 >. , <. 3 , 9 >. } -> 3 R 9 )

  proof
    cR
    c2
    c6
    cop
    #
    c3
    c9
    cop
    #
    cpr
    #
    wceq
    #
    @1
    cR
    wcel
    c3
    c9
    cR
    wbr
    @3
    @1
    @2
    cR
    @0
    @1
    c3
    c9
    opex
    prid2
    @3
    id
    syl5eleqr
    c3
    c9
    cR
    df-br
    sylibr
end
