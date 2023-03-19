include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "c0g.mm"
include "wb.mm"
include "eqeq1d.mm"
include "oveqrspc2v.mm"
include "ancom2s.mm"
include "anbi12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "eleq2d.mm"
include "raleqdv.mm"
include "3bitr3d.mm"
include "iotabidv.mm"
include "eqid.mm"
include "grpidval.mm"
include "3eqtr4g.mm"

theorem grpidpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vw: setvar w
  let vz: setvar z
  assume grpidpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume grpidpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume grpidpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint K w
  disjoint K z
  disjoint ph w
  disjoint ph z
  disjoint L w
  disjoint L z
  assert |- ( ph -> ( 0g ` K ) = ( 0g ` L ) )

  proof
    wph
    vx
    cv
    #
    cK
    cbs
    cfv
    #
    wcel
    #
    @0
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @0
    @4
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    wa
    #
    vx
    cio
    @0
    cL
    cbs
    cfv
    #
    wcel
    #
    @0
    @3
    cL
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @0
    @14
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @12
    wral
    #
    wa
    #
    vx
    cio
    cK
    c0g
    cfv
    #
    cL
    c0g
    cfv
    #
    wph
    @11
    @21
    vx
    wph
    @0
    cB
    wcel
    #
    @9
    vy
    cB
    wral
    #
    wa
    @24
    @19
    vy
    cB
    wral
    #
    wa
    @11
    @21
    wph
    @24
    @25
    @26
    wph
    @24
    wa
    @9
    @19
    vy
    cB
    wph
    @24
    @3
    cB
    wcel
    #
    @9
    @19
    wb
    wph
    @24
    @27
    wa
    wa
    #
    @6
    @16
    @8
    @18
    @28
    @5
    @15
    @3
    grpidpropd.3
    eqeq1d
    @28
    @7
    @17
    @3
    wph
    @27
    @24
    @7
    @17
    wceq
    wph
    vz
    vw
    cB
    cB
    @4
    @14
    @3
    @0
    wph
    vx
    vy
    cB
    cB
    @4
    @14
    vz
    cv
    vw
    cv
    grpidpropd.3
    oveqrspc2v
    oveqrspc2v
    ancom2s
    eqeq1d
    anbi12d
    anassrs
    ralbidva
    pm5.32da
    wph
    @24
    @2
    @25
    @10
    wph
    cB
    @1
    @0
    grpidpropd.1
    eleq2d
    wph
    @9
    vy
    cB
    @1
    grpidpropd.1
    raleqdv
    anbi12d
    wph
    @24
    @13
    @26
    @20
    wph
    cB
    @12
    @0
    grpidpropd.2
    eleq2d
    wph
    @19
    vy
    cB
    @12
    grpidpropd.2
    raleqdv
    anbi12d
    3bitr3d
    iotabidv
    vy
    @1
    @4
    vx
    cK
    @22
    @1
    eqid
    @4
    eqid
    @22
    eqid
    grpidval
    vy
    @12
    @14
    vx
    cL
    @23
    @12
    eqid
    @14
    eqid
    @23
    eqid
    grpidval
    3eqtr4g
end
