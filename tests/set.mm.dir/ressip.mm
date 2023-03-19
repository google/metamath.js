include "cip.mm"
include "c8.mm"
include "df-ip.mm"
include "8nn.mm"
include "1lt8.mm"
include "resslem.mm"

theorem ressip
  let cA: class A
  let cG: class G
  let cH: class H
  let c.xi: class .,
  let cV: class V
  assume resssca.1: |- H = ( G |`s A )
  assume ressip.2: |- ., = ( .i ` G )


  assert |- ( A e. V -> ., = ( .i ` H ) )

  proof
    cA
    c.xi
    cH
    cip
    c8
    cV
    cG
    resssca.1
    ressip.2
    df-ip
    8nn
    1lt8
    resslem
end
