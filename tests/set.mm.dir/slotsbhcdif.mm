include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "chom.mm"
include "wne.mm"
include "cco.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"
include "c4.mm"
include "cdc.mm"
include "1re.mm"
include "4nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ltneii.mm"
include "homndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "c5.mm"
include "5nn0.mm"
include "ccondx.mm"
include "deccl.mm"
include "nn0rei.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "3pm3.2i.mm"

theorem slotsbhcdif



  assert |- ( ( Base ` ndx ) =/= ( Hom ` ndx ) /\ ( Base ` ndx ) =/= ( comp ` ndx ) /\ ( Hom ` ndx ) =/= ( comp ` ndx ) )

  proof
    cnx
    cbs
    cfv
    #
    cnx
    chom
    cfv
    #
    wne
    @0
    cnx
    cco
    cfv
    #
    wne
    @1
    @2
    wne
    @0
    c1
    @1
    cbs
    c1
    df-base
    1nn
    ndxarg
    #
    c1
    c1
    c4
    cdc
    #
    @1
    c1
    @4
    1re
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    ltneii
    homndx
    neeqtrri
    eqnetri
    @0
    c1
    @2
    @3
    c1
    c1
    c5
    cdc
    #
    @2
    c1
    @5
    1re
    c1
    c5
    c1
    1nn
    5nn0
    1nn0
    1lt10
    declti
    ltneii
    ccondx
    neeqtrri
    eqnetri
    @1
    @4
    @2
    homndx
    @4
    @5
    @2
    @4
    @5
    @4
    c1
    c4
    1nn0
    4nn0
    deccl
    nn0rei
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    ltneii
    ccondx
    neeqtrri
    eqnetri
    3pm3.2i
end
