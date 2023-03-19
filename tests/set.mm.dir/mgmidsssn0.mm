include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "csn.mm"
include "wi.mm"
include "wss.mm"
include "simpr.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "adantl.mm"
include "ismgmid.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "velsn.mm"
include "sylibr.mm"
include "expr.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "syl5eqss.mm"

theorem mgmidsssn0
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cO: class O
  let cV: class V
  let c.0: class .0.
  let vz: setvar z
  assume mgmidsssn0.b: |- B = ( Base ` G )
  assume mgmidsssn0.z: |- .0. = ( 0g ` G )
  assume mgmidsssn0.p: |- .+ = ( +g ` G )
  assume mgmidsssn0.o: |- O = { x e. B | A. y e. B ( ( x .+ y ) = y /\ ( y .+ x ) = y ) }

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint V x
  disjoint .0. x
  disjoint .0. y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint .+ z
  disjoint .0. z
  assert |- ( G e. V -> O C_ { .0. } )

  proof
    cG
    cV
    wcel
    #
    cO
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @1
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    crab
    #
    c.0
    csn
    #
    mgmidsssn0.o
    @0
    @8
    @1
    @10
    wcel
    #
    wi
    #
    vx
    cB
    wral
    @9
    @10
    wss
    @0
    @12
    vx
    cB
    @0
    @1
    cB
    wcel
    #
    @8
    @11
    @0
    @13
    @8
    wa
    #
    wa
    #
    @1
    c.0
    wceq
    @11
    @15
    c.0
    @1
    @15
    @14
    c.0
    @1
    wceq
    @0
    @14
    simpr
    @15
    vy
    cB
    c.pl
    @1
    vz
    cG
    c.0
    mgmidsssn0.b
    mgmidsssn0.z
    mgmidsssn0.p
    @14
    vz
    cv
    #
    @2
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @16
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    vz
    cB
    wrex
    @0
    @22
    @8
    vz
    @1
    cB
    @16
    @1
    wceq
    #
    @21
    @7
    vy
    cB
    @23
    @18
    @4
    @20
    @6
    @23
    @17
    @3
    @2
    @16
    @1
    @2
    c.pl
    oveq1
    eqeq1d
    @23
    @19
    @5
    @2
    @16
    @1
    @2
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    adantl
    ismgmid
    mpbid
    eqcomd
    vx
    c.0
    velsn
    sylibr
    expr
    ralrimiva
    @8
    vx
    cB
    @10
    rabss
    sylibr
    syl5eqss
end
