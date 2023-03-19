include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "c5.mm"
include "2re.mm"
include "2lt5.mm"
include "ltneii.mm"
include "resvlem.mm"

theorem resvplusg
  let cA: class A
  let c.pl: class .+
  let cG: class G
  let cH: class H
  let cV: class V
  assume resvbas.1: |- H = ( G |`v A )
  assume resvplusg.2: |- .+ = ( +g ` G )


  assert |- ( A e. V -> .+ = ( +g ` H ) )

  proof
    cA
    c.pl
    cH
    cplusg
    c2
    cV
    cG
    resvbas.1
    resvplusg.2
    df-plusg
    2nn
    c2
    c5
    2re
    2lt5
    ltneii
    resvlem
end
