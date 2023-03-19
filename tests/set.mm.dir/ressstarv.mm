include "cstv.mm"
include "c4.mm"
include "df-starv.mm"
include "4nn.mm"
include "1lt4.mm"
include "resslem.mm"

theorem ressstarv
  let cA: class A
  let cR: class R
  let cS: class S
  let c.as: class .*
  let cV: class V
  assume ressmulr.1: |- S = ( R |`s A )
  assume ressstarv.2: |- .* = ( *r ` R )


  assert |- ( A e. V -> .* = ( *r ` S ) )

  proof
    cA
    c.as
    cS
    cstv
    c4
    cV
    cR
    ressmulr.1
    ressstarv.2
    df-starv
    4nn
    1lt4
    resslem
end
