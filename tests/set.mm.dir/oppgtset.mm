include "cts.mm"
include "cfv.mm"
include "c9.mm"
include "df-tset.mm"
include "9nn.mm"
include "c2.mm"
include "2re.mm"
include "2lt9.mm"
include "gtneii.mm"
include "oppglem.mm"
include "eqtri.mm"

theorem oppgtset
  let cR: class R
  let cJ: class J
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppgtset.2: |- J = ( TopSet ` R )


  assert |- J = ( TopSet ` O )

  proof
    cJ
    cR
    cts
    cfv
    cO
    cts
    cfv
    oppgtset.2
    cR
    cts
    c9
    cO
    oppgbas.1
    df-tset
    9nn
    c2
    c9
    2re
    2lt9
    gtneii
    oppglem
    eqtri
end
