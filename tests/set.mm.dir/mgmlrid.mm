include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wcel.mm"
include "eqid.mm"
include "ismgmid.mm"
include "mpbiri.mm"
include "simprd.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem mgmlrid
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let ve: setvar e
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let cU: class U
  assume ismgmid.b: |- B = ( Base ` G )
  assume ismgmid.o: |- .0. = ( 0g ` G )
  assume ismgmid.p: |- .+ = ( +g ` G )
  assume mgmidcl.e: |- ( ph -> E. e e. B A. x e. B ( ( e .+ x ) = x /\ ( x .+ e ) = x ) )

  disjoint e x
  disjoint .+ e
  disjoint .+ x
  disjoint .0. e
  disjoint .0. x
  disjoint B e
  disjoint B x
  disjoint G e
  disjoint G x
  disjoint X x
  disjoint U e
  disjoint U x
  assert |- ( ( ph /\ X e. B ) -> ( ( .0. .+ X ) = X /\ ( X .+ .0. ) = X ) )

  proof
    wph
    c.0
    vx
    cv
    #
    c.pl
    co
    #
    @0
    wceq
    #
    @0
    c.0
    c.pl
    co
    #
    @0
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    c.0
    cX
    c.pl
    co
    #
    cX
    wceq
    #
    cX
    c.0
    c.pl
    co
    #
    cX
    wceq
    #
    wa
    #
    wph
    c.0
    cB
    wcel
    #
    @6
    wph
    @12
    @6
    wa
    c.0
    c.0
    wceq
    c.0
    eqid
    wph
    vx
    cB
    c.pl
    c.0
    ve
    cG
    c.0
    ismgmid.b
    ismgmid.o
    ismgmid.p
    mgmidcl.e
    ismgmid
    mpbiri
    simprd
    @5
    @11
    vx
    cX
    cB
    @0
    cX
    wceq
    #
    @2
    @8
    @4
    @10
    @13
    @1
    @7
    @0
    cX
    @0
    cX
    c.0
    c.pl
    oveq2
    @13
    id
    #
    eqeq12d
    @13
    @3
    @9
    @0
    cX
    @0
    cX
    c.0
    c.pl
    oveq1
    @14
    eqeq12d
    anbi12d
    rspccva
    sylan
end
