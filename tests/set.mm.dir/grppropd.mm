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
include "wa.mm"
include "cgrp.mm"
include "mndpropd.mm"
include "wb.mm"
include "grpidpropd.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "anass1rs.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "rexeqdv.mm"
include "raleqbidv.mm"
include "3bitr3d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "isgrp.mm"
include "3bitr4g.mm"

theorem grppropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume grppropd.1: |- ( ph -> B = ( Base ` K ) )
  assume grppropd.2: |- ( ph -> B = ( Base ` L ) )
  assume grppropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( K e. Grp <-> L e. Grp ) )

  proof
    wph
    cK
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    cK
    c0g
    cfv
    #
    wceq
    #
    vx
    cK
    cbs
    cfv
    #
    wrex
    #
    vy
    @7
    wral
    #
    wa
    cL
    cmnd
    wcel
    #
    @1
    @2
    cL
    cplusg
    cfv
    #
    co
    #
    cL
    c0g
    cfv
    #
    wceq
    #
    vx
    cL
    cbs
    cfv
    #
    wrex
    #
    vy
    @15
    wral
    #
    wa
    cK
    cgrp
    wcel
    cL
    cgrp
    wcel
    wph
    @0
    @10
    @9
    @17
    wph
    vx
    vy
    cB
    cK
    cL
    grppropd.1
    grppropd.2
    grppropd.3
    mndpropd
    wph
    @6
    vx
    cB
    wrex
    #
    vy
    cB
    wral
    @14
    vx
    cB
    wrex
    #
    vy
    cB
    wral
    @9
    @17
    wph
    @18
    @19
    vy
    cB
    wph
    @2
    cB
    wcel
    #
    wa
    @6
    @14
    vx
    cB
    wph
    @1
    cB
    wcel
    #
    @20
    @6
    @14
    wb
    wph
    @21
    @20
    wa
    #
    wa
    @4
    @12
    @5
    @13
    grppropd.3
    wph
    @5
    @13
    wceq
    @22
    wph
    vx
    vy
    cB
    cK
    cL
    grppropd.1
    grppropd.2
    grppropd.3
    grpidpropd
    adantr
    eqeq12d
    anass1rs
    rexbidva
    ralbidva
    wph
    @18
    @8
    vy
    cB
    @7
    grppropd.1
    wph
    @6
    vx
    cB
    @7
    grppropd.1
    rexeqdv
    raleqbidv
    wph
    @19
    @16
    vy
    cB
    @15
    grppropd.2
    wph
    @14
    vx
    cB
    @15
    grppropd.2
    rexeqdv
    raleqbidv
    3bitr3d
    anbi12d
    @7
    @3
    vx
    cK
    @5
    vy
    @7
    eqid
    @3
    eqid
    @5
    eqid
    isgrp
    @15
    @11
    vx
    cL
    @13
    vy
    @15
    eqid
    @11
    eqid
    @13
    eqid
    isgrp
    3bitr4g
end
