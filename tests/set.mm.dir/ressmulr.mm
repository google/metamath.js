include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "1lt3.mm"
include "resslem.mm"

theorem ressmulr
  let cA: class A
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cV: class V
  assume ressmulr.1: |- S = ( R |`s A )
  assume ressmulr.2: |- .x. = ( .r ` R )


  assert |- ( A e. V -> .x. = ( .r ` S ) )

  proof
    cA
    c.x
    cS
    cmulr
    c3
    cV
    cR
    ressmulr.1
    ressmulr.2
    df-mulr
    3nn
    1lt3
    resslem
end
