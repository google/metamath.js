include "chil.mm"
include "wf.mm"
include "chod.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "ch0o.mm"
include "cif.mm"
include "oveq1.mm"
include "coeq1d.mm"
include "coeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "coeq2.mm"
include "oveq12d.mm"
include "ho0f.mm"
include "elimf.mm"
include "hocsubdiri.mm"
include "dedth3h.mm"

theorem hocsubdir
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( R : ~H --> ~H /\ S : ~H --> ~H /\ T : ~H --> ~H ) -> ( ( R -op S ) o. T ) = ( ( R o. T ) -op ( S o. T ) ) )

  proof
    chil
    chil
    cR
    wf
    #
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    cR
    cS
    chod
    co
    #
    cT
    ccom
    #
    cR
    cT
    ccom
    #
    cS
    cT
    ccom
    #
    chod
    co
    #
    wceq
    @0
    cR
    ch0o
    cif
    #
    cS
    chod
    co
    #
    cT
    ccom
    #
    @8
    cT
    ccom
    #
    @6
    chod
    co
    #
    wceq
    @8
    @1
    cS
    ch0o
    cif
    #
    chod
    co
    #
    cT
    ccom
    #
    @11
    @13
    cT
    ccom
    #
    chod
    co
    #
    wceq
    @14
    @2
    cT
    ch0o
    cif
    #
    ccom
    #
    @8
    @18
    ccom
    #
    @13
    @18
    ccom
    #
    chod
    co
    #
    wceq
    cR
    cS
    cT
    ch0o
    ch0o
    ch0o
    cR
    @8
    wceq
    #
    @4
    @10
    @7
    @12
    @23
    @3
    @9
    cT
    cR
    @8
    cS
    chod
    oveq1
    coeq1d
    @23
    @5
    @11
    @6
    chod
    cR
    @8
    cT
    coeq1
    oveq1d
    eqeq12d
    cS
    @13
    wceq
    #
    @10
    @15
    @12
    @17
    @24
    @9
    @14
    cT
    cS
    @13
    @8
    chod
    oveq2
    coeq1d
    @24
    @6
    @16
    @11
    chod
    cS
    @13
    cT
    coeq1
    oveq2d
    eqeq12d
    cT
    @18
    wceq
    #
    @15
    @19
    @17
    @22
    cT
    @18
    @14
    coeq2
    @25
    @11
    @20
    @16
    @21
    chod
    cT
    @18
    @8
    coeq2
    cT
    @18
    @13
    coeq2
    oveq12d
    eqeq12d
    @8
    @13
    @18
    chil
    chil
    cR
    ch0o
    ho0f
    elimf
    chil
    chil
    cS
    ch0o
    ho0f
    elimf
    chil
    chil
    cT
    ch0o
    ho0f
    elimf
    hocsubdiri
    dedth3h
end
