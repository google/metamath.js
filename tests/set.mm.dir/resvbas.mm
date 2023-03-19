include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "c5.mm"
include "1re.mm"
include "1lt5.mm"
include "ltneii.mm"
include "resvlem.mm"

theorem resvbas
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let cV: class V
  assume resvbas.1: |- H = ( G |`v A )
  assume resvbas.2: |- B = ( Base ` G )


  assert |- ( A e. V -> B = ( Base ` H ) )

  proof
    cA
    cB
    cH
    cbs
    c1
    cV
    cG
    resvbas.1
    resvbas.2
    df-base
    1nn
    c1
    c5
    1re
    1lt5
    ltneii
    resvlem
end
