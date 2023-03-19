include "chil.mm"
include "wf.mm"
include "chos.mm"
include "co.mm"
include "wceq.mm"
include "ch0o.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ho0f.mm"
include "elimf.mm"
include "hoaddassi.mm"
include "dedth3h.mm"

theorem hoaddass
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( R : ~H --> ~H /\ S : ~H --> ~H /\ T : ~H --> ~H ) -> ( ( R +op S ) +op T ) = ( R +op ( S +op T ) ) )

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
    chos
    co
    #
    cT
    chos
    co
    #
    cR
    cS
    cT
    chos
    co
    #
    chos
    co
    #
    wceq
    @0
    cR
    ch0o
    cif
    #
    cS
    chos
    co
    #
    cT
    chos
    co
    #
    @7
    @5
    chos
    co
    #
    wceq
    @7
    @1
    cS
    ch0o
    cif
    #
    chos
    co
    #
    cT
    chos
    co
    #
    @7
    @11
    cT
    chos
    co
    #
    chos
    co
    #
    wceq
    @12
    @2
    cT
    ch0o
    cif
    #
    chos
    co
    #
    @7
    @11
    @16
    chos
    co
    #
    chos
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
    @7
    wceq
    #
    @4
    @9
    @6
    @10
    @20
    @3
    @8
    cT
    chos
    cR
    @7
    cS
    chos
    oveq1
    oveq1d
    cR
    @7
    @5
    chos
    oveq1
    eqeq12d
    cS
    @11
    wceq
    #
    @9
    @13
    @10
    @15
    @21
    @8
    @12
    cT
    chos
    cS
    @11
    @7
    chos
    oveq2
    oveq1d
    @21
    @5
    @14
    @7
    chos
    cS
    @11
    cT
    chos
    oveq1
    oveq2d
    eqeq12d
    cT
    @16
    wceq
    #
    @13
    @17
    @15
    @19
    cT
    @16
    @12
    chos
    oveq2
    @22
    @14
    @18
    @7
    chos
    cT
    @16
    @11
    chos
    oveq2
    oveq2d
    eqeq12d
    @7
    @11
    @16
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
    hoaddassi
    dedth3h
end
