include "chil.mm"
include "wf.mm"
include "chod.mm"
include "co.mm"
include "ch0o.mm"
include "chos.mm"
include "wceq.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ho0f.mm"
include "elimf.mm"
include "ho0subi.mm"
include "dedth2h.mm"

theorem ho0sub
  let cS: class S
  let cT: class T


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( S -op T ) = ( S +op ( 0hop -op T ) ) )

  proof
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
    cS
    cT
    chod
    co
    #
    cS
    ch0o
    cT
    chod
    co
    #
    chos
    co
    #
    wceq
    @0
    cS
    ch0o
    cif
    #
    cT
    chod
    co
    #
    @5
    @3
    chos
    co
    #
    wceq
    @5
    @1
    cT
    ch0o
    cif
    #
    chod
    co
    #
    @5
    ch0o
    @8
    chod
    co
    #
    chos
    co
    #
    wceq
    cS
    cT
    ch0o
    ch0o
    cS
    @5
    wceq
    @2
    @6
    @4
    @7
    cS
    @5
    cT
    chod
    oveq1
    cS
    @5
    @3
    chos
    oveq1
    eqeq12d
    cT
    @8
    wceq
    #
    @6
    @9
    @7
    @11
    cT
    @8
    @5
    chod
    oveq2
    @12
    @3
    @10
    @5
    chos
    cT
    @8
    ch0o
    chod
    oveq2
    oveq2d
    eqeq12d
    @5
    @8
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
    ho0subi
    dedth2h
end
