include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "c5.mm"
include "3re.mm"
include "3lt5.mm"
include "ltneii.mm"
include "resvlem.mm"

theorem resvmulr
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cV: class V
  assume resvbas.1: |- H = ( G |`v A )
  assume resvmulr.2: |- .x. = ( .r ` G )


  assert |- ( A e. V -> .x. = ( .r ` H ) )

  proof
    cA
    c.x
    cH
    cmulr
    c3
    cV
    cG
    resvbas.1
    resvmulr.2
    df-mulr
    3nn
    c3
    c5
    3re
    3lt5
    ltneii
    resvlem
end
