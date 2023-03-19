include "cvsca.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "c5.mm"
include "5re.mm"
include "5lt6.mm"
include "gtneii.mm"
include "resvlem.mm"

theorem resvvsca
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cV: class V
  assume resvbas.1: |- H = ( G |`v A )
  assume resvvsca.2: |- .x. = ( .s ` G )


  assert |- ( A e. V -> .x. = ( .s ` H ) )

  proof
    cA
    c.x
    cH
    cvsca
    c6
    cV
    cG
    resvbas.1
    resvvsca.2
    df-vsca
    6nn
    c5
    c6
    5re
    5lt6
    gtneii
    resvlem
end
