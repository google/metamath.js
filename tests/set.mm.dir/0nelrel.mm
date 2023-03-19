include "wrel.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "0nelxp.mm"
include "a1i.mm"
include "ssneldd.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem 0nelrel
  let cR: class R


  assert |- ( Rel R -> (/) e/ R )

  proof
    cR
    wrel
    #
    c0
    cR
    wcel
    wn
    c0
    cR
    wnel
    @0
    cR
    cvv
    cvv
    cxp
    #
    c0
    @0
    cR
    @1
    wss
    cR
    df-rel
    biimpi
    c0
    @1
    wcel
    wn
    @0
    cvv
    cvv
    0nelxp
    a1i
    ssneldd
    c0
    cR
    df-nel
    sylibr
end
