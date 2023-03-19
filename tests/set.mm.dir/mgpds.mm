include "cds.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "2re.mm"
include "1nn.mm"
include "2nn0.mm"
include "2lt10.mm"
include "declti.mm"
include "gtneii.mm"
include "mgplem.mm"
include "eqtri.mm"

theorem mgpds
  let cB: class B
  let cR: class R
  let cM: class M
  assume mgpbas.1: |- M = ( mulGrp ` R )
  assume mgpds.2: |- B = ( dist ` R )


  assert |- B = ( dist ` M )

  proof
    cB
    cR
    cds
    cfv
    cM
    cds
    cfv
    mgpds.2
    cR
    cds
    cM
    c1
    c2
    cdc
    #
    mgpbas.1
    df-ds
    c1
    c2
    1nn0
    2nn
    decnncl
    c2
    @0
    2re
    c1
    c2
    c2
    1nn
    2nn0
    2nn0
    2lt10
    declti
    gtneii
    mgplem
    eqtri
end
