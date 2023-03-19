include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wral.mm"
include "cgrp.mm"
include "ralrimiva.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "eqid.mm"
include "isgrp.mm"
include "sylanbrc.mm"

theorem isgrpd2e
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let cN: class N
  assume isgrpd2.b: |- ( ph -> B = ( Base ` G ) )
  assume isgrpd2.p: |- ( ph -> .+ = ( +g ` G ) )
  assume isgrpd2.z: |- ( ph -> .0. = ( 0g ` G ) )
  assume isgrpd2.g: |- ( ph -> G e. Mnd )
  assume isgrpd2e.n: |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = .0. )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint .0. y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint N y
  assert |- ( ph -> G e. Grp )

  proof
    wph
    cG
    cmnd
    wcel
    vy
    cv
    #
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    vy
    cG
    cbs
    cfv
    #
    wrex
    #
    vx
    @6
    wral
    #
    cG
    cgrp
    wcel
    isgrpd2.g
    wph
    @0
    @1
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wral
    @8
    wph
    @11
    vx
    cB
    isgrpd2e.n
    ralrimiva
    wph
    @11
    @7
    vx
    cB
    @6
    isgrpd2.b
    wph
    @10
    @5
    vy
    cB
    @6
    isgrpd2.b
    wph
    @9
    @3
    c.0
    @4
    wph
    c.pl
    @2
    @0
    @1
    isgrpd2.p
    oveqd
    isgrpd2.z
    eqeq12d
    rexeqbidv
    raleqbidv
    mpbid
    @6
    @2
    vy
    cG
    @4
    vx
    @6
    eqid
    @2
    eqid
    @4
    eqid
    isgrp
    sylanbrc
end
