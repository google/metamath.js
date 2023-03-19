include "cch.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "cho.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "h0elch.mm"
include "elimel.mm"
include "pjhmopi.mm"
include "dedth.mm"

theorem pjhmop
  let cH: class H


  assert |- ( H e. CH -> ( projh ` H ) e. HrmOp )

  proof
    cH
    cch
    wcel
    #
    cH
    cpjh
    cfv
    #
    cho
    wcel
    @0
    cH
    c0h
    cif
    #
    cpjh
    cfv
    #
    cho
    wcel
    cH
    c0h
    cH
    @2
    wceq
    @1
    @3
    cho
    cH
    @2
    cpjh
    fveq2
    eleq1d
    @2
    cH
    c0h
    cch
    h0elch
    elimel
    pjhmopi
    dedth
end
