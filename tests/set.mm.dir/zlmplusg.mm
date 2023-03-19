include "cplusg.mm"
include "cfv.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt5.mm"
include "zlmlem.mm"
include "eqtri.mm"

theorem zlmplusg
  let c.pl: class .+
  let cG: class G
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )
  assume zlmplusg.2: |- .+ = ( +g ` G )


  assert |- .+ = ( +g ` W )

  proof
    c.pl
    cG
    cplusg
    cfv
    cW
    cplusg
    cfv
    zlmplusg.2
    cplusg
    cG
    c2
    cW
    zlmbas.w
    df-plusg
    2nn
    2lt5
    zlmlem
    eqtri
end
