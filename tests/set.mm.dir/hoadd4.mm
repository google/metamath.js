include "chil.mm"
include "wf.mm"
include "wa.mm"
include "chos.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "hoadd32.mm"
include "oveq1d.mm"
include "3expa.mm"
include "adantrr.mm"
include "hoaddcl.mm"
include "hoaddass.mm"
include "3expb.mm"
include "sylan.mm"
include "an4s.mm"
include "3eqtr3d.mm"

theorem hoadd4
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( ( R : ~H --> ~H /\ S : ~H --> ~H ) /\ ( T : ~H --> ~H /\ U : ~H --> ~H ) ) -> ( ( R +op S ) +op ( T +op U ) ) = ( ( R +op T ) +op ( S +op U ) ) )

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
    wa
    #
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cU
    wf
    #
    wa
    #
    wa
    cR
    cS
    chos
    co
    #
    cT
    chos
    co
    #
    cU
    chos
    co
    #
    cR
    cT
    chos
    co
    #
    cS
    chos
    co
    #
    cU
    chos
    co
    #
    @6
    cT
    cU
    chos
    co
    chos
    co
    #
    @9
    cS
    cU
    chos
    co
    chos
    co
    #
    @2
    @3
    @8
    @11
    wceq
    #
    @4
    @0
    @1
    @3
    @14
    @0
    @1
    @3
    w3a
    @7
    @10
    cU
    chos
    cR
    cS
    cT
    hoadd32
    oveq1d
    3expa
    adantrr
    @2
    chil
    chil
    @6
    wf
    #
    @5
    @8
    @12
    wceq
    #
    cR
    cS
    hoaddcl
    @15
    @3
    @4
    @16
    @6
    cT
    cU
    hoaddass
    3expb
    sylan
    @0
    @3
    @1
    @4
    @11
    @13
    wceq
    #
    @0
    @3
    wa
    chil
    chil
    @9
    wf
    #
    @1
    @4
    wa
    @17
    cR
    cT
    hoaddcl
    @18
    @1
    @4
    @17
    @9
    cS
    cU
    hoaddass
    3expb
    sylan
    an4s
    3eqtr3d
end
