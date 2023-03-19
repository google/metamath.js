include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wfo.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "fveq2.mm"
include "foeq1.mm"
include "syl.mm"
include "foeq3.mm"
include "h0elch.mm"
include "elimel.mm"
include "pjfoi.mm"
include "dedth2v.mm"

theorem pjhfo
  let cH: class H


  assert |- ( H e. CH -> ( projh ` H ) : ~H -onto-> H )

  proof
    cH
    cch
    wcel
    #
    chil
    cH
    cH
    cpjh
    cfv
    #
    wfo
    #
    chil
    cH
    @0
    cH
    c0h
    cif
    #
    cpjh
    cfv
    #
    wfo
    #
    chil
    @3
    @4
    wfo
    cH
    cH
    c0h
    c0h
    cH
    @3
    wceq
    @1
    @4
    wceq
    @2
    @5
    wb
    cH
    @3
    cpjh
    fveq2
    chil
    cH
    @1
    @4
    foeq1
    syl
    cH
    @3
    chil
    @4
    foeq3
    @3
    cH
    c0h
    cch
    h0elch
    elimel
    pjfoi
    dedth2v
end
