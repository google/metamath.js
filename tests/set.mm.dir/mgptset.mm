include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "9nn.mm"
include "c2.mm"
include "2re.mm"
include "2lt9.mm"
include "gtneii.mm"
include "mgplem.mm"

theorem mgptset
  let cR: class R
  let cM: class M
  assume mgpbas.1: |- M = ( mulGrp ` R )


  assert |- ( TopSet ` R ) = ( TopSet ` M )

  proof
    cR
    cts
    cM
    c9
    mgpbas.1
    df-tset
    9nn
    c2
    c9
    2re
    2lt9
    gtneii
    mgplem
end
