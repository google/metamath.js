include "cmnd.mm"
include "wcel.mm"
include "csn.mm"
include "mgmidsssn0.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "mndidcl.mm"
include "mndlrid.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "eqssd.mm"

theorem gsumvallem2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cO: class O
  let c.0: class .0.
  assume gsumvallem2.b: |- B = ( Base ` G )
  assume gsumvallem2.z: |- .0. = ( 0g ` G )
  assume gsumvallem2.p: |- .+ = ( +g ` G )
  assume gsumvallem2.o: |- O = { x e. B | A. y e. B ( ( x .+ y ) = y /\ ( y .+ x ) = y ) }

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint .0. x
  disjoint .0. y
  assert |- ( G e. Mnd -> O = { .0. } )

  proof
    cG
    cmnd
    wcel
    #
    cO
    c.0
    csn
    vx
    vy
    cB
    c.pl
    cG
    cO
    cmnd
    c.0
    gsumvallem2.b
    gsumvallem2.z
    gsumvallem2.p
    gsumvallem2.o
    mgmidsssn0
    @0
    c.0
    cO
    @0
    c.0
    cB
    wcel
    c.0
    vy
    cv
    #
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    c.0
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    c.0
    cO
    wcel
    cB
    cG
    c.0
    gsumvallem2.b
    gsumvallem2.z
    mndidcl
    @0
    @6
    vy
    cB
    cB
    c.pl
    cG
    @1
    c.0
    gsumvallem2.b
    gsumvallem2.p
    gsumvallem2.z
    mndlrid
    ralrimiva
    vx
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
    vy
    cB
    wral
    @7
    vx
    c.0
    cB
    cO
    @8
    c.0
    wceq
    #
    @13
    @6
    vy
    cB
    @14
    @10
    @3
    @12
    @5
    @14
    @9
    @2
    @1
    @8
    c.0
    @1
    c.pl
    oveq1
    eqeq1d
    @14
    @11
    @4
    @1
    @8
    c.0
    @1
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    gsumvallem2.o
    elrab2
    sylanbrc
    snssd
    eqssd
end
