include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "wral.mm"
include "cmgm.mm"
include "wa.mm"
include "wceq.mm"
include "simpl.mm"
include "wi.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "adantr.mm"
include "impcom.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "syl12anc.mm"
include "eleq1d.mm"
include "2ralbidva.mm"
include "eqtr3d.mm"
include "raleqbidv.mm"
include "bitrd.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wex.mm"
include "n0.mm"
include "eqid.mm"
include "ismgmn0.mm"
include "syl6bi.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "mpd.mm"
include "3bitr4d.mm"

theorem mgmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let va: setvar a
  let vk: setvar k
  assume mgmpropd.k: |- ( ph -> B = ( Base ` K ) )
  assume mgmpropd.l: |- ( ph -> B = ( Base ` L ) )
  assume mgmpropd.b: |- ( ph -> B =/= (/) )
  assume mgmpropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint a x
  disjoint a y
  disjoint K a
  disjoint L a
  disjoint a ph
  disjoint k x
  assert |- ( ph -> ( K e. Mgm <-> L e. Mgm ) )

  proof
    wph
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
    cbs
    cfv
    #
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    @0
    @1
    cL
    cplusg
    cfv
    #
    co
    #
    cL
    cbs
    cfv
    #
    wcel
    #
    vy
    @9
    wral
    #
    vx
    @9
    wral
    #
    cK
    cmgm
    wcel
    #
    cL
    cmgm
    wcel
    #
    wph
    @6
    @8
    @4
    wcel
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    @12
    wph
    @5
    @15
    vx
    vy
    @4
    @4
    wph
    @0
    @4
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    wa
    #
    @3
    @8
    @4
    @20
    wph
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @3
    @8
    wceq
    wph
    @19
    simpl
    @19
    wph
    @21
    @17
    wph
    @21
    wi
    @18
    wph
    @17
    @21
    wph
    @4
    cB
    @0
    wph
    cB
    @4
    mgmpropd.k
    eqcomd
    #
    eleq2d
    biimpcd
    adantr
    impcom
    wph
    @19
    @22
    wph
    @18
    @22
    @17
    wph
    @18
    @22
    wph
    @4
    cB
    @1
    @23
    eleq2d
    biimpd
    adantld
    imp
    mgmpropd.p
    syl12anc
    eleq1d
    2ralbidva
    wph
    @16
    @11
    vx
    @4
    @9
    wph
    cB
    @4
    @9
    mgmpropd.k
    mgmpropd.l
    eqtr3d
    #
    wph
    @15
    @10
    vy
    @4
    @9
    @24
    wph
    @4
    @9
    @8
    @24
    eleq2d
    raleqbidv
    raleqbidv
    bitrd
    wph
    cB
    c0
    wne
    #
    @13
    @6
    wb
    #
    mgmpropd.b
    @25
    va
    cv
    #
    cB
    wcel
    #
    va
    wex
    #
    wph
    @26
    va
    cB
    n0
    #
    wph
    @28
    @26
    va
    wph
    @28
    @27
    @4
    wcel
    @26
    wph
    cB
    @4
    @27
    mgmpropd.k
    eleq2d
    vx
    vy
    @27
    @4
    cK
    @2
    @4
    eqid
    @2
    eqid
    ismgmn0
    syl6bi
    exlimdv
    syl5bi
    mpd
    wph
    @25
    @14
    @12
    wb
    #
    mgmpropd.b
    @25
    @29
    wph
    @31
    @30
    wph
    @28
    @31
    va
    wph
    @28
    @27
    @9
    wcel
    @31
    wph
    cB
    @9
    @27
    mgmpropd.l
    eleq2d
    vx
    vy
    @27
    @9
    cL
    @7
    @9
    eqid
    @7
    eqid
    ismgmn0
    syl6bi
    exlimdv
    syl5bi
    mpd
    3bitr4d
end
