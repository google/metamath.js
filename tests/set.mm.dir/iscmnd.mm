include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "ccmn.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "mpbi2and.mm"
include "eqid.mm"
include "iscmn.mm"
include "sylibr.mm"

theorem iscmnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume iscmnd.b: |- ( ph -> B = ( Base ` G ) )
  assume iscmnd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume iscmnd.g: |- ( ph -> G e. Mnd )
  assume iscmnd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) = ( y .+ x ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> G e. CMnd )

  proof
    wph
    cG
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    @1
    @3
    co
    #
    wceq
    #
    vy
    cG
    cbs
    cfv
    #
    wral
    #
    vx
    @7
    wral
    #
    wa
    #
    cG
    ccmn
    wcel
    wph
    @0
    @1
    @2
    c.pl
    co
    #
    @2
    @1
    c.pl
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @10
    iscmnd.g
    wph
    @13
    vx
    vy
    cB
    cB
    wph
    @1
    cB
    wcel
    @2
    cB
    wcel
    @13
    iscmnd.c
    3expib
    ralrimivv
    wph
    @15
    @9
    @0
    wph
    @14
    @8
    vx
    cB
    @7
    iscmnd.b
    wph
    @13
    @6
    vy
    cB
    @7
    iscmnd.b
    wph
    @11
    @4
    @12
    @5
    wph
    c.pl
    @3
    @1
    @2
    iscmnd.p
    oveqd
    wph
    c.pl
    @3
    @2
    @1
    iscmnd.p
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    anbi2d
    mpbi2and
    vx
    vy
    @7
    @3
    cG
    @7
    eqid
    @3
    eqid
    iscmn
    sylibr
end
