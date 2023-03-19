include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cfn.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "isfusgr.mm"
include "cv.mm"
include "cop.mm"
include "ccusgr.mm"
include "wex.mm"
include "cusgrexg.mm"
include "adantl.mm"
include "cedg.mm"
include "cvtx.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "vex.mm"
include "opvtxfv.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "eqid.mm"
include "sizusglecusg.mm"
include "adantlr.mm"
include "wi.mm"
include "cusgrsize.mm"
include "breq2.mm"
include "biimpd.mm"
include "syl.mm"
include "expcom.mm"
include "imp.mm"
include "mpd.mm"
include "exlimddv.mm"
include "sylbi.mm"

theorem fusgrmaxsize
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  assume fusgrmaxsize.v: |- V = ( Vtx ` G )
  assume fusgrmaxsize.e: |- E = ( Edg ` G )


  assert |- ( G e. FinUSGraph -> ( # ` E ) <_ ( ( # ` V ) _C 2 ) )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    wa
    #
    cE
    chash
    cfv
    #
    cV
    chash
    cfv
    c2
    cbc
    co
    #
    cle
    wbr
    #
    cG
    cV
    fusgrmaxsize.v
    isfusgr
    @2
    cV
    ve
    cv
    #
    cop
    #
    ccusgr
    wcel
    #
    @5
    ve
    @1
    @8
    ve
    wex
    @0
    ve
    cV
    cfn
    cusgrexg
    adantl
    @2
    @8
    wa
    @3
    @7
    cedg
    cfv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @5
    @0
    @8
    @11
    @1
    cE
    @9
    cG
    @7
    cV
    fusgrmaxsize.v
    fusgrmaxsize.e
    @7
    cvtx
    cfv
    #
    cV
    cV
    cvv
    wcel
    @6
    cvv
    wcel
    @12
    cV
    wceq
    cV
    cG
    cvtx
    cfv
    cvv
    fusgrmaxsize.v
    cG
    cvtx
    fvex
    eqeltri
    ve
    vex
    @6
    cV
    cvv
    cvv
    opvtxfv
    mp2an
    eqcomi
    #
    @9
    eqid
    #
    sizusglecusg
    adantlr
    @2
    @8
    @11
    @5
    wi
    #
    @1
    @8
    @15
    wi
    @0
    @8
    @1
    @15
    @8
    @1
    wa
    @10
    @4
    wceq
    #
    @15
    @9
    @7
    cV
    @13
    @14
    cusgrsize
    @16
    @11
    @5
    @10
    @4
    @3
    cle
    breq2
    biimpd
    syl
    expcom
    adantl
    imp
    mpd
    exlimddv
    sylbi
end
