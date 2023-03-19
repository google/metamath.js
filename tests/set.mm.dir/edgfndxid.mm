include "wcel.mm"
include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "c1.mm"
include "c8.mm"
include "cdc.mm"
include "id.mm"
include "df-edgf.mm"
include "1nn0.mm"
include "8nn.mm"
include "decnncl.mm"
include "strndxid.mm"
include "eqcomd.mm"

theorem edgfndxid
  let cG: class G
  let cV: class V


  assert |- ( G e. V -> ( .ef ` G ) = ( G ` ( .ef ` ndx ) ) )

  proof
    cG
    cV
    wcel
    #
    cnx
    cedgf
    cfv
    cG
    cfv
    cG
    cedgf
    cfv
    @0
    cG
    cedgf
    c1
    c8
    cdc
    cV
    @0
    id
    df-edgf
    c1
    c8
    1nn0
    8nn
    decnncl
    strndxid
    eqcomd
end
