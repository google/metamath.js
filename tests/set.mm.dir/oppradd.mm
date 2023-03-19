include "cplusg.mm"
include "cfv.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt3.mm"
include "opprlem.mm"
include "eqtri.mm"

theorem oppradd
  let c.pl: class .+
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume oppradd.2: |- .+ = ( +g ` R )


  assert |- .+ = ( +g ` O )

  proof
    c.pl
    cR
    cplusg
    cfv
    cO
    cplusg
    cfv
    oppradd.2
    cR
    cplusg
    c2
    cO
    opprbas.1
    df-plusg
    2nn
    2lt3
    opprlem
    eqtri
end
