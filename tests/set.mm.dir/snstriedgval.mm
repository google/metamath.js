include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "ciedg.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "c0.mm"
include "wceq.mm"
include "iedgval.mm"
include "a1i.mm"
include "wn.mm"
include "necom.mm"
include "fvex.mm"
include "funsndifnop.mm"
include "sylbi.mm"
include "iffalsed.mm"
include "cop.mm"
include "csn.mm"
include "snex.mm"
include "syl5eqel.mm"
include "edgfndxid.mm"
include "mp2b.mm"
include "cdm.mm"
include "slotsbaseefdif.mm"
include "nesymi.mm"
include "elsn.mm"
include "sylnibr.mm"
include "dmeqi.mm"
include "dmsnopg.mm"
include "mp1i.mm"
include "syl5eq.mm"
include "neleqtrrd.mm"
include "ndmfv.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem snstriedgval
  let cG: class G
  let cV: class V
  assume snstrvtxval.v: |- V e. _V
  assume snstrvtxval.g: |- G = { <. ( Base ` ndx ) , V >. }


  assert |- ( V =/= ( Base ` ndx ) -> ( iEdg ` G ) = (/) )

  proof
    cV
    cnx
    cbs
    cfv
    #
    wne
    #
    cG
    ciedg
    cfv
    #
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    c2nd
    cfv
    #
    cG
    cedgf
    cfv
    #
    cif
    #
    @5
    c0
    @2
    @6
    wceq
    @1
    cG
    iedgval
    a1i
    @1
    @3
    @4
    @5
    @1
    @0
    cV
    wne
    @3
    wn
    cV
    @0
    necom
    @0
    cV
    cG
    cnx
    cbs
    fvex
    snstrvtxval.v
    snstrvtxval.g
    funsndifnop
    sylbi
    iffalsed
    @1
    @5
    cnx
    cedgf
    cfv
    #
    cG
    cfv
    #
    c0
    cG
    @0
    cV
    cop
    #
    csn
    #
    wceq
    #
    cG
    cvv
    wcel
    @5
    @8
    wceq
    snstrvtxval.g
    @11
    cG
    @10
    cvv
    snstrvtxval.g
    @10
    cvv
    wcel
    @11
    @9
    snex
    a1i
    syl5eqel
    cG
    cvv
    edgfndxid
    mp2b
    @1
    @7
    cG
    cdm
    #
    wcel
    wn
    @8
    c0
    wceq
    @1
    @12
    @0
    csn
    #
    @7
    @1
    @7
    @0
    wceq
    #
    @7
    @13
    wcel
    @14
    wn
    @1
    @0
    @7
    slotsbaseefdif
    nesymi
    a1i
    @7
    @0
    cnx
    cedgf
    fvex
    elsn
    sylnibr
    @1
    @12
    @10
    cdm
    #
    @13
    cG
    @10
    snstrvtxval.g
    dmeqi
    cV
    cvv
    wcel
    @15
    @13
    wceq
    @1
    snstrvtxval.v
    @0
    cV
    cvv
    dmsnopg
    mp1i
    syl5eq
    neleqtrrd
    @7
    cG
    ndmfv
    syl
    syl5eq
    3eqtrd
end
