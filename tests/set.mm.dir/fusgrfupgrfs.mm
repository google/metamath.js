include "cfusgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cfn.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgrupgr.mm"
include "syl.mm"
include "fusgrvtxfi.mm"
include "cedg.mm"
include "cfv.mm"
include "fusgrfis.mm"
include "wb.mm"
include "eqid.mm"
include "usgredgffibi.mm"
include "mpbid.mm"
include "3jca.mm"

theorem fusgrfupgrfs
  let cG: class G
  let cI: class I
  let cV: class V
  assume fusgrfupgrfs.v: |- V = ( Vtx ` G )
  assume fusgrfupgrfs.i: |- I = ( iEdg ` G )


  assert |- ( G e. FinUSGraph -> ( G e. UPGraph /\ V e. Fin /\ I e. Fin ) )

  proof
    cG
    cfusgr
    wcel
    #
    cG
    cupgr
    wcel
    #
    cV
    cfn
    wcel
    cI
    cfn
    wcel
    #
    @0
    cG
    cusgr
    wcel
    #
    @1
    cG
    fusgrusgr
    #
    cG
    usgrupgr
    syl
    cG
    cV
    fusgrfupgrfs.v
    fusgrvtxfi
    @0
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    @2
    cG
    fusgrfis
    @0
    @3
    @6
    @2
    wb
    @4
    @5
    cG
    cI
    fusgrfupgrfs.i
    @5
    eqid
    usgredgffibi
    syl
    mpbid
    3jca
end
