include "crab.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wa.mm"
include "anbi12i.mm"
include "adantr.mm"
include "simprll.mm"
include "simprrl.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "an4.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "issubm.mm"
include "mpbir3and.mm"

theorem issubmd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let c.0: class .0.
  assume issubmd.b: |- B = ( Base ` M )
  assume issubmd.p: |- .+ = ( +g ` M )
  assume issubmd.z: |- .0. = ( 0g ` M )
  assume issubmd.m: |- ( ph -> M e. Mnd )
  assume issubmd.cz: |- ( ph -> ch )
  assume issubmd.cp: |- ( ( ph /\ ( ( x e. B /\ y e. B ) /\ ( th /\ ta ) ) ) -> et )
  assume issubmd.ch: |- ( z = .0. -> ( ps <-> ch ) )
  assume issubmd.th: |- ( z = x -> ( ps <-> th ) )
  assume issubmd.ta: |- ( z = y -> ( ps <-> ta ) )
  assume issubmd.et: |- ( z = ( x .+ y ) -> ( ps <-> et ) )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps y
  disjoint .+ z
  disjoint .0. z
  disjoint ch z
  disjoint et z
  disjoint ta z
  disjoint th z
  assert |- ( ph -> { z e. B | ps } e. ( SubMnd ` M ) )

  proof
    wph
    wps
    vz
    cB
    crab
    #
    cM
    csubmnd
    cfv
    wcel
    #
    @0
    cB
    wss
    #
    c.0
    @0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @2
    wph
    wps
    vz
    cB
    ssrab2
    a1i
    wph
    c.0
    cB
    wcel
    #
    wch
    @3
    wph
    cM
    cmnd
    wcel
    #
    @9
    issubmd.m
    cB
    cM
    c.0
    issubmd.b
    issubmd.z
    mndidcl
    syl
    issubmd.cz
    wps
    wch
    vz
    c.0
    cB
    issubmd.ch
    elrab
    sylanbrc
    wph
    @7
    vx
    vy
    @0
    @0
    @4
    @0
    wcel
    #
    @5
    @0
    wcel
    #
    wa
    wph
    @4
    cB
    wcel
    #
    wth
    wa
    #
    @5
    cB
    wcel
    #
    wta
    wa
    #
    wa
    #
    @7
    @11
    @14
    @12
    @16
    wps
    wth
    vz
    @4
    cB
    issubmd.th
    elrab
    wps
    wta
    vz
    @5
    cB
    issubmd.ta
    elrab
    anbi12i
    wph
    @17
    wa
    #
    @6
    cB
    wcel
    #
    wet
    @7
    @18
    @10
    @13
    @15
    @19
    wph
    @10
    @17
    issubmd.m
    adantr
    wph
    @13
    wth
    @16
    simprll
    wph
    @14
    @15
    wta
    simprrl
    cB
    c.pl
    cM
    @4
    @5
    issubmd.b
    issubmd.p
    mndcl
    syl3anc
    @17
    wph
    @13
    @15
    wa
    wth
    wta
    wa
    wa
    wet
    @13
    wth
    @15
    wta
    an4
    issubmd.cp
    sylan2b
    wps
    wet
    vz
    @6
    cB
    issubmd.et
    elrab
    sylanbrc
    sylan2b
    ralrimivva
    wph
    @10
    @1
    @2
    @3
    @8
    w3a
    wb
    issubmd.m
    vx
    vy
    cB
    c.pl
    @0
    cM
    c.0
    issubmd.b
    issubmd.z
    issubmd.p
    issubm
    syl
    mpbir3and
end
