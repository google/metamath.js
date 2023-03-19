include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ismgmid.mm"
include "mpbi2and.mm"
include "eqcomd.mm"

theorem ismgmid2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let ve: setvar e
  let cX: class X
  assume ismgmid.b: |- B = ( Base ` G )
  assume ismgmid.o: |- .0. = ( 0g ` G )
  assume ismgmid.p: |- .+ = ( +g ` G )
  assume ismgmid2.u: |- ( ph -> U e. B )
  assume ismgmid2.l: |- ( ( ph /\ x e. B ) -> ( U .+ x ) = x )
  assume ismgmid2.r: |- ( ( ph /\ x e. B ) -> ( x .+ U ) = x )

  disjoint .+ x
  disjoint .0. x
  disjoint B x
  disjoint G x
  disjoint U x
  disjoint ph x
  disjoint e x
  disjoint .+ e
  disjoint .0. e
  disjoint B e
  disjoint G e
  disjoint X x
  disjoint U e
  assert |- ( ph -> U = .0. )

  proof
    wph
    c.0
    cU
    wph
    cU
    cB
    wcel
    #
    cU
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
    cU
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
    c.0
    cU
    wceq
    ismgmid2.u
    wph
    @6
    vx
    cB
    wph
    @1
    cB
    wcel
    wa
    @3
    @5
    ismgmid2.l
    ismgmid2.r
    jca
    ralrimiva
    #
    wph
    vx
    cB
    c.pl
    cU
    ve
    cG
    c.0
    ismgmid.b
    ismgmid.o
    ismgmid.p
    wph
    @0
    @7
    ve
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
    @9
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
    ve
    cB
    wrex
    ismgmid2.u
    @8
    @15
    @7
    ve
    cU
    cB
    @9
    cU
    wceq
    #
    @14
    @6
    vx
    cB
    @16
    @11
    @3
    @13
    @5
    @16
    @10
    @2
    @1
    @9
    cU
    @1
    c.pl
    oveq1
    eqeq1d
    @16
    @12
    @4
    @1
    @9
    cU
    @1
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    syl2anc
    ismgmid
    mpbi2and
    eqcomd
end
