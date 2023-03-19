include "chil.mm"
include "wf.mm"
include "wa.mm"
include "chos.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "chod.mm"
include "wceq.mm"
include "honegdi.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mpan.mm"
include "anim12i.mm"
include "hoadd4.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "hoaddcl.mm"
include "honegsub.mm"
include "syl2an.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem hosub4
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( ( R : ~H --> ~H /\ S : ~H --> ~H ) /\ ( T : ~H --> ~H /\ U : ~H --> ~H ) ) -> ( ( R +op S ) -op ( T +op U ) ) = ( ( R -op T ) +op ( S -op U ) ) )

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
    #
    cR
    cS
    chos
    co
    #
    c1
    cneg
    #
    cT
    cU
    chos
    co
    #
    chot
    co
    #
    chos
    co
    #
    cR
    @8
    cT
    chot
    co
    #
    chos
    co
    #
    cS
    @8
    cU
    chot
    co
    #
    chos
    co
    #
    chos
    co
    #
    @7
    @9
    chod
    co
    #
    cR
    cT
    chod
    co
    #
    cS
    cU
    chod
    co
    #
    chos
    co
    @6
    @11
    @7
    @12
    @14
    chos
    co
    #
    chos
    co
    #
    @16
    @6
    @10
    @20
    @7
    chos
    @5
    @10
    @20
    wceq
    @2
    cT
    cU
    honegdi
    adantl
    oveq2d
    @5
    @2
    chil
    chil
    @12
    wf
    #
    chil
    chil
    @14
    wf
    #
    wa
    @21
    @16
    wceq
    @3
    @22
    @4
    @23
    @8
    cc
    wcel
    #
    @3
    @22
    neg1cn
    @8
    cT
    homulcl
    mpan
    @24
    @4
    @23
    neg1cn
    @8
    cU
    homulcl
    mpan
    anim12i
    cR
    cS
    @12
    @14
    hoadd4
    sylan2
    eqtrd
    @2
    chil
    chil
    @7
    wf
    chil
    chil
    @9
    wf
    @11
    @17
    wceq
    @5
    cR
    cS
    hoaddcl
    cT
    cU
    hoaddcl
    @7
    @9
    honegsub
    syl2an
    @6
    @13
    @18
    @15
    @19
    chos
    @0
    @3
    @13
    @18
    wceq
    @1
    @4
    cR
    cT
    honegsub
    ad2ant2r
    @1
    @4
    @15
    @19
    wceq
    @0
    @3
    cS
    cU
    honegsub
    ad2ant2l
    oveq12d
    3eqtr3d
end
