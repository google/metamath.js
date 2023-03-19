include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wa.mm"
include "chash.mm"
include "cn0.mm"
include "eqid.mm"
include "isfusgr.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "hashclb.mm"
include "mp1i.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isfusgrcl
  let cG: class G


  assert |- ( G e. FinUSGraph <-> ( G e. USGraph /\ ( # ` ( Vtx ` G ) ) e. NN0 ) )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    wa
    @0
    @1
    chash
    cfv
    cn0
    wcel
    #
    wa
    cG
    @1
    @1
    eqid
    isfusgr
    @0
    @2
    @3
    @1
    cvv
    wcel
    @2
    @3
    wb
    @0
    cG
    cvtx
    fvex
    @1
    cvv
    hashclb
    mp1i
    pm5.32i
    bitri
end
