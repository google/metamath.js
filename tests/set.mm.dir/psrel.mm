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
include "simp1d.mm"

theorem psrel
  let cA: class A


  assert |- ( A e. PosetRel -> Rel A )

  proof
    cA
    cps
    wcel
    #
    cA
    wrel
    #
    cA
    cA
    ccom
    cA
    wss
    #
    cA
    cA
    ccnv
    cin
    cid
    cA
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
    cA
    isps
    ibi
    simp1d
end
