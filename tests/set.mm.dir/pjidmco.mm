include "cch.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "c0h.mm"
include "cif.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "eqeq12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "pjidmcoi.mm"
include "dedth.mm"

theorem pjidmco
  let cH: class H


  assert |- ( H e. CH -> ( ( projh ` H ) o. ( projh ` H ) ) = ( projh ` H ) )

  proof
    cH
    cch
    wcel
    #
    cH
    cpjh
    cfv
    #
    @1
    ccom
    #
    @1
    wceq
    @0
    cH
    c0h
    cif
    #
    cpjh
    cfv
    #
    @4
    ccom
    #
    @4
    wceq
    cH
    c0h
    cH
    @3
    wceq
    #
    @2
    @5
    @1
    @4
    @6
    @1
    @4
    @1
    @4
    cH
    @3
    cpjh
    fveq2
    #
    @7
    coeq12d
    @7
    eqeq12d
    @3
    cH
    c0h
    cch
    h0elch
    elimel
    pjidmcoi
    dedth
end
