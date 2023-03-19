include "csca.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "1lt5.mm"
include "resslem.mm"

theorem resssca
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume resssca.1: |- H = ( G |`s A )
  assume resssca.2: |- F = ( Scalar ` G )


  assert |- ( A e. V -> F = ( Scalar ` H ) )

  proof
    cA
    cF
    cH
    csca
    c5
    cV
    cG
    resssca.1
    resssca.2
    df-sca
    5nn
    1lt5
    resslem
end
