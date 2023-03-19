include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrmo.mm"
include "weq.mm"
include "wi.mm"
include "wcel.mm"
include "simpl.mm"
include "ralimi.mm"
include "simpr.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "oveq2.mm"
include "sylan9req.mm"
include "an42s.mm"
include "ex.mm"
include "syl2ani.mm"
include "rgen2a.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rmo4.mm"
include "mpbir.mm"

theorem mgmidmo
  let vx: setvar x
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let vw: setvar w

  disjoint u x
  disjoint B u
  disjoint B x
  disjoint .+ u
  disjoint .+ x
  disjoint u w
  disjoint w x
  disjoint B w
  disjoint .+ w
  assert |- E* u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x )

  proof
    vu
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @0
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    vu
    cB
    wrmo
    @7
    vw
    cv
    #
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @8
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    vu
    vw
    weq
    #
    wi
    #
    vw
    cB
    wral
    vu
    cB
    wral
    @16
    vu
    vw
    cB
    @7
    @0
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    @3
    vx
    cB
    wral
    #
    @12
    vx
    cB
    wral
    #
    @15
    @14
    @6
    @3
    vx
    cB
    @3
    @5
    simpl
    ralimi
    @13
    @12
    vx
    cB
    @10
    @12
    simpr
    ralimi
    @19
    @20
    @21
    wa
    @15
    @17
    @21
    @18
    @20
    @15
    @17
    @21
    wa
    @18
    @20
    wa
    @0
    @0
    @8
    c.pl
    co
    #
    @8
    @12
    @22
    @0
    wceq
    vx
    @0
    cB
    vx
    vu
    weq
    #
    @11
    @22
    @1
    @0
    @1
    @0
    @8
    c.pl
    oveq1
    @23
    id
    eqeq12d
    rspcva
    @3
    @22
    @8
    wceq
    vx
    @8
    cB
    vx
    vw
    weq
    #
    @2
    @22
    @1
    @8
    @1
    @8
    @0
    c.pl
    oveq2
    @24
    id
    eqeq12d
    rspcva
    sylan9req
    an42s
    ex
    syl2ani
    rgen2a
    @7
    @14
    vu
    vw
    cB
    @15
    @6
    @13
    vx
    cB
    @15
    @3
    @10
    @5
    @12
    @15
    @2
    @9
    @1
    @0
    @8
    @1
    c.pl
    oveq1
    eqeq1d
    @15
    @4
    @11
    @1
    @0
    @8
    @1
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rmo4
    mpbir
end
