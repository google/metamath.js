include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "ismgmid.mm"
include "mpbiri.mm"
include "simpld.mm"

theorem mgmidcl
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let ve: setvar e
  let cG: class G
  let c.0: class .0.
  let cX: class X
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
  assert |- ( ph -> .0. e. B )

  proof
    wph
    c.0
    cB
    wcel
    #
    c.0
    vx
    cv
    #
    c.pl
    co
    @1
    wceq
    @1
    c.0
    c.pl
    co
    @1
    wceq
    wa
    vx
    cB
    wral
    #
    wph
    @0
    @2
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
    simpld
end
