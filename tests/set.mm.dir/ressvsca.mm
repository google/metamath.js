include "cvsca.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "1lt6.mm"
include "resslem.mm"

theorem ressvsca
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cV: class V
  assume resssca.1: |- H = ( G |`s A )
  assume ressvsca.2: |- .x. = ( .s ` G )


  assert |- ( A e. V -> .x. = ( .s ` H ) )

  proof
    cA
    c.x
    cH
    cvsca
    c6
    cV
    cG
    resssca.1
    ressvsca.2
    df-vsca
    6nn
    1lt6
    resslem
end
