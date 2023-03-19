include "cple.mm"
include "cfv.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "df-ple.mm"
include "10nn.mm"
include "c2.mm"
include "2re.mm"
include "2lt10.mm"
include "gtneii.mm"
include "oppglem.mm"
include "eqtri.mm"

theorem oppgle
  let cR: class R
  let c.le: class .<_
  let cO: class O
  assume oppglt.1: |- O = ( oppG ` R )
  assume oppgle.2: |- .<_ = ( le ` R )


  assert |- .<_ = ( le ` O )

  proof
    c.le
    cR
    cple
    cfv
    cO
    cple
    cfv
    oppgle.2
    cR
    cple
    c1
    cc0
    cdc
    #
    cO
    oppglt.1
    df-ple
    10nn
    c2
    @0
    2re
    2lt10
    gtneii
    oppglem
    eqtri
end
