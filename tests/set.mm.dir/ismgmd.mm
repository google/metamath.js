include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wral.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "wb.mm"
include "eqid.mm"
include "ismgm.mm"
include "syl.mm"
include "mpbird.mm"

theorem ismgmd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume ismgmd.b: |- ( ph -> B = ( Base ` G ) )
  assume ismgmd.0: |- ( ph -> G e. V )
  assume ismgmd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume ismgmd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> G e. Mgm )

  proof
    wph
    cG
    cmgm
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
    cG
    cbs
    cfv
    #
    wcel
    #
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    wph
    @1
    @2
    c.pl
    co
    #
    cB
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @8
    wph
    @10
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
    @10
    ismgmd.c
    3expb
    ralrimivva
    wph
    @11
    @7
    vx
    cB
    @5
    ismgmd.b
    wph
    @10
    @6
    vy
    cB
    @5
    ismgmd.b
    wph
    @9
    @4
    cB
    @5
    wph
    c.pl
    @3
    @1
    @2
    ismgmd.p
    oveqd
    ismgmd.b
    eleq12d
    raleqbidv
    raleqbidv
    mpbid
    wph
    cG
    cV
    wcel
    @0
    @8
    wb
    ismgmd.0
    vx
    vy
    @5
    cG
    cV
    @3
    @5
    eqid
    @3
    eqid
    ismgm
    syl
    mpbird
end
