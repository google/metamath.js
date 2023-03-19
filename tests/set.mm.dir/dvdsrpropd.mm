include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "cdsr.mm"
include "wb.mm"
include "anassrs.mm"
include "eqeq1d.mm"
include "an32s.mm"
include "rexbidva.mm"
include "pm5.32da.mm"
include "eleq2d.mm"
include "rexeqdv.mm"
include "anbi12d.mm"
include "3bitr3d.mm"
include "opabbidv.mm"
include "eqid.mm"
include "dvdsrval.mm"
include "3eqtr4g.mm"

theorem dvdsrpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vz: setvar z
  assume rngidpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume rngidpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume rngidpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L z
  disjoint ph z
  assert |- ( ph -> ( ||r ` K ) = ( ||r ` L ) )

  proof
    wph
    vy
    cv
    #
    cK
    cbs
    cfv
    #
    wcel
    #
    vx
    cv
    #
    @0
    cK
    cmulr
    cfv
    #
    co
    #
    vz
    cv
    #
    wceq
    #
    vx
    @1
    wrex
    #
    wa
    #
    vy
    vz
    copab
    @0
    cL
    cbs
    cfv
    #
    wcel
    #
    @3
    @0
    cL
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    vx
    @10
    wrex
    #
    wa
    #
    vy
    vz
    copab
    cK
    cdsr
    cfv
    #
    cL
    cdsr
    cfv
    #
    wph
    @9
    @16
    vy
    vz
    wph
    @0
    cB
    wcel
    #
    @7
    vx
    cB
    wrex
    #
    wa
    @19
    @14
    vx
    cB
    wrex
    #
    wa
    @9
    @16
    wph
    @19
    @20
    @21
    wph
    @19
    wa
    @7
    @14
    vx
    cB
    wph
    @3
    cB
    wcel
    #
    @19
    @7
    @14
    wb
    wph
    @22
    wa
    @19
    wa
    @5
    @13
    @6
    wph
    @22
    @19
    @5
    @13
    wceq
    rngidpropd.3
    anassrs
    eqeq1d
    an32s
    rexbidva
    pm5.32da
    wph
    @19
    @2
    @20
    @8
    wph
    cB
    @1
    @0
    rngidpropd.1
    eleq2d
    wph
    @7
    vx
    cB
    @1
    rngidpropd.1
    rexeqdv
    anbi12d
    wph
    @19
    @11
    @21
    @15
    wph
    cB
    @10
    @0
    rngidpropd.2
    eleq2d
    wph
    @14
    vx
    cB
    @10
    rngidpropd.2
    rexeqdv
    anbi12d
    3bitr3d
    opabbidv
    vy
    vz
    vx
    @1
    @17
    cK
    @4
    @1
    eqid
    @17
    eqid
    @4
    eqid
    dvdsrval
    vy
    vz
    vx
    @10
    @18
    cL
    @12
    @10
    eqid
    @18
    eqid
    @12
    eqid
    dvdsrval
    3eqtr4g
end
