include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "9nn.mm"
include "1lt9.mm"
include "resslem.mm"

theorem resstset
  let cA: class A
  let cG: class G
  let cH: class H
  let cJ: class J
  let cV: class V
  assume resstset.1: |- H = ( G |`s A )
  assume resstset.2: |- J = ( TopSet ` G )


  assert |- ( A e. V -> J = ( TopSet ` H ) )

  proof
    cA
    cJ
    cH
    cts
    c9
    cV
    cG
    resstset.1
    resstset.2
    df-tset
    9nn
    1lt9
    resslem
end
