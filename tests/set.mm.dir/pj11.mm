include "cch.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "pj11i.mm"
include "dedth2h.mm"

theorem pj11
  let cG: class G
  let cH: class H


  assert |- ( ( G e. CH /\ H e. CH ) -> ( ( projh ` G ) = ( projh ` H ) <-> G = H ) )

  proof
    cG
    cch
    wcel
    #
    cH
    cch
    wcel
    #
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    wceq
    #
    cG
    cH
    wceq
    #
    wb
    @0
    cG
    c0h
    cif
    #
    cpjh
    cfv
    #
    @3
    wceq
    #
    @6
    cH
    wceq
    #
    wb
    @7
    @1
    cH
    c0h
    cif
    #
    cpjh
    cfv
    #
    wceq
    #
    @6
    @10
    wceq
    #
    wb
    cG
    cH
    c0h
    c0h
    cG
    @6
    wceq
    #
    @4
    @8
    @5
    @9
    @14
    @2
    @7
    @3
    cG
    @6
    cpjh
    fveq2
    eqeq1d
    cG
    @6
    cH
    eqeq1
    bibi12d
    cH
    @10
    wceq
    #
    @8
    @12
    @9
    @13
    @15
    @3
    @11
    @7
    cH
    @10
    cpjh
    fveq2
    eqeq2d
    cH
    @10
    @6
    eqeq2
    bibi12d
    @6
    @10
    cG
    c0h
    cch
    h0elch
    elimel
    cH
    c0h
    cch
    h0elch
    elimel
    pj11i
    dedth2h
end
