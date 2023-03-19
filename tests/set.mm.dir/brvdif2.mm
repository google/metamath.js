include "cvv.mm"
include "cdif.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "brvdif.mm"
include "df-br.mm"
include "xchbinx.mm"

theorem brvdif2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A ( _V \ R ) B <-> -. <. A , B >. e. R )

  proof
    cA
    cB
    cvv
    cR
    cdif
    wbr
    cA
    cB
    cR
    wbr
    cA
    cB
    cop
    cR
    wcel
    cA
    cB
    cR
    brvdif
    cA
    cB
    cR
    df-br
    xchbinx
end
