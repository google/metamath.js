include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "chod.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "ch0o.mm"
include "cif.mm"
include "coeq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "coeq2d.mm"
include "coeq2.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "0lnop.mm"
include "elimel.mm"
include "ho0f.mm"
include "elimf.mm"
include "hoddii.mm"
include "dedth3h.mm"

theorem hoddi
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( R e. LinOp /\ S : ~H --> ~H /\ T : ~H --> ~H ) -> ( R o. ( S -op T ) ) = ( ( R o. S ) -op ( R o. T ) ) )

  proof
    cR
    clo
    wcel
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
    cT
    chod
    co
    #
    ccom
    #
    cR
    cS
    ccom
    #
    cR
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
    @3
    ccom
    #
    @8
    cS
    ccom
    #
    @8
    cT
    ccom
    #
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
    cT
    chod
    co
    #
    ccom
    #
    @8
    @13
    ccom
    #
    @11
    chod
    co
    #
    wceq
    @8
    @13
    @2
    cT
    ch0o
    cif
    #
    chod
    co
    #
    ccom
    #
    @16
    @8
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
    @9
    @7
    @12
    cR
    @8
    @3
    coeq1
    @23
    @5
    @10
    @6
    @11
    chod
    cR
    @8
    cS
    coeq1
    cR
    @8
    cT
    coeq1
    oveq12d
    eqeq12d
    cS
    @13
    wceq
    #
    @9
    @15
    @12
    @17
    @24
    @3
    @14
    @8
    cS
    @13
    cT
    chod
    oveq1
    coeq2d
    @24
    @10
    @16
    @11
    chod
    cS
    @13
    @8
    coeq2
    oveq1d
    eqeq12d
    cT
    @18
    wceq
    #
    @15
    @20
    @17
    @22
    @25
    @14
    @19
    @8
    cT
    @18
    @13
    chod
    oveq2
    coeq2d
    @25
    @11
    @21
    @16
    chod
    cT
    @18
    @8
    coeq2
    oveq2d
    eqeq12d
    @8
    @13
    @18
    cR
    ch0o
    clo
    0lnop
    elimel
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
    hoddii
    dedth3h
end
