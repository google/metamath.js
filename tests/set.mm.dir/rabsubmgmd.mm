include "crab.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wa.mm"
include "elrab.mm"
include "anbi12i.mm"
include "cmgm.mm"
include "adantr.mm"
include "simprll.mm"
include "simprrl.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "simpl.mm"
include "anim12i.mm"
include "simpr.mm"
include "jca.mm"
include "sylan2.mm"
include "sylanbrc.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "wb.mm"
include "issubmgm.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem rabsubmgmd
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let vk: setvar k
  assume rabsubmgmd.b: |- B = ( Base ` M )
  assume rabsubmgmd.p: |- .+ = ( +g ` M )
  assume rabsubmgmd.m: |- ( ph -> M e. Mgm )
  assume rabsubmgmd.cp: |- ( ( ph /\ ( ( x e. B /\ y e. B ) /\ ( th /\ ta ) ) ) -> et )
  assume rabsubmgmd.th: |- ( z = x -> ( ps <-> th ) )
  assume rabsubmgmd.ta: |- ( z = y -> ( ps <-> ta ) )
  assume rabsubmgmd.et: |- ( z = ( x .+ y ) -> ( ps <-> et ) )

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
  disjoint et z
  disjoint ta z
  disjoint th z
  disjoint k x
  assert |- ( ph -> { z e. B | ps } e. ( SubMgm ` M ) )

  proof
    wph
    wps
    vz
    cB
    crab
    #
    cM
    csubmgm
    cfv
    wcel
    #
    @0
    cB
    wss
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
    @6
    vx
    vy
    @0
    @0
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    wph
    @3
    cB
    wcel
    #
    wth
    wa
    #
    @4
    cB
    wcel
    #
    wta
    wa
    #
    wa
    #
    @6
    @8
    @11
    @9
    @13
    wps
    wth
    vz
    @3
    cB
    rabsubmgmd.th
    elrab
    wps
    wta
    vz
    @4
    cB
    rabsubmgmd.ta
    elrab
    anbi12i
    wph
    @14
    wa
    #
    @5
    cB
    wcel
    #
    wet
    @6
    @15
    cM
    cmgm
    wcel
    #
    @10
    @12
    @16
    wph
    @17
    @14
    rabsubmgmd.m
    adantr
    wph
    @10
    wth
    @13
    simprll
    wph
    @11
    @12
    wta
    simprrl
    cB
    cM
    @3
    @4
    c.pl
    rabsubmgmd.b
    rabsubmgmd.p
    mgmcl
    syl3anc
    @14
    wph
    @10
    @12
    wa
    #
    wth
    wta
    wa
    #
    wa
    wet
    @14
    @18
    @19
    @11
    @10
    @13
    @12
    @10
    wth
    simpl
    @12
    wta
    simpl
    anim12i
    @11
    wth
    @13
    wta
    @10
    wth
    simpr
    @12
    wta
    simpr
    anim12i
    jca
    rabsubmgmd.cp
    sylan2
    wps
    wet
    vz
    @5
    cB
    rabsubmgmd.et
    elrab
    sylanbrc
    sylan2b
    ralrimivva
    wph
    @17
    @1
    @2
    @7
    wa
    wb
    rabsubmgmd.m
    vx
    vy
    cB
    c.pl
    @0
    cM
    rabsubmgmd.b
    rabsubmgmd.p
    issubmgm
    syl
    mpbir2and
end
