include "cps.mm"
include "wcel.mm"
include "wrel.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "cin.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "isps.mm"
include "ibi.mm"
include "simp2d.mm"

theorem pstr2
  let cR: class R


  assert |- ( R e. PosetRel -> ( R o. R ) C_ R )

  proof
    cR
    cps
    wcel
    #
    cR
    wrel
    #
    cR
    cR
    ccom
    cR
    wss
    #
    cR
    cR
    ccnv
    cin
    cid
    cR
    cuni
    cuni
    cres
    wceq
    #
    @0
    @1
    @2
    @3
    w3a
    cps
    cR
    isps
    ibi
    simp2d
end
