include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "wf1o.mm"
include "cnbgr.mm"
include "co.mm"
include "cpr.mm"
include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "usgrf1o.mm"
include "wa.mm"
include "prcom.mm"
include "cedg.mm"
include "eqid.mm"
include "nbusgreledg.mm"
include "ciedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "eqtri.mm"
include "a1i.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "biimpa.mm"
include "syl5eqelr.mm"
include "f1ocnvfv2.mm"
include "syl2an2r.mm"

theorem usgrnbcnvfv
  let cG: class G
  let cI: class I
  let cK: class K
  let cN: class N
  assume usgrnbcnvfv.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. USGraph /\ N e. ( G NeighbVtx K ) ) -> ( I ` ( `' I ` { K , N } ) ) = { K , N } )

  proof
    cG
    cusgr
    wcel
    #
    cI
    cdm
    #
    cI
    crn
    #
    cI
    wf1o
    cN
    cG
    cK
    cnbgr
    co
    wcel
    #
    cK
    cN
    cpr
    #
    @2
    wcel
    @4
    cI
    ccnv
    cfv
    cI
    cfv
    @4
    wceq
    cI
    cG
    usgrnbcnvfv.i
    usgrf1o
    @0
    @3
    wa
    @4
    cN
    cK
    cpr
    #
    @2
    cN
    cK
    prcom
    @0
    @3
    @5
    @2
    wcel
    #
    @0
    @3
    @5
    cG
    cedg
    cfv
    #
    wcel
    @6
    @7
    cG
    cK
    cN
    @7
    eqid
    nbusgreledg
    @0
    @7
    @2
    @5
    @7
    @2
    wceq
    @0
    @7
    cG
    ciedg
    cfv
    #
    crn
    @2
    cG
    edgval
    @8
    cI
    cI
    @8
    usgrnbcnvfv.i
    eqcomi
    rneqi
    eqtri
    a1i
    eleq2d
    bitrd
    biimpa
    syl5eqelr
    @1
    @2
    @4
    cI
    f1ocnvfv2
    syl2an2r
end
