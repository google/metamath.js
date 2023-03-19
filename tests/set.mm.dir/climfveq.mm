include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "climdm.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylibr.mm"
include "wb.mm"
include "climeldmeq.mm"
include "adantr.mm"
include "mpbid.mm"
include "sylib.mm"
include "cz.mm"
include "cv.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "climeq.mm"
include "climuni.mm"
include "syl2anc.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "simpr.mm"
include "mtbid.mm"
include "syl.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem climfveq
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume climfveq.1: |- Z = ( ZZ>= ` M )
  assume climfveq.2: |- ( ph -> F e. V )
  assume climfveq.3: |- ( ph -> G e. W )
  assume climfveq.4: |- ( ph -> M e. ZZ )
  assume climfveq.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint Z k
  disjoint k ph
  assert |- ( ph -> ( ~~> ` F ) = ( ~~> ` G ) )

  proof
    wph
    cF
    cli
    cdm
    #
    wcel
    #
    cF
    cli
    cfv
    #
    cG
    cli
    cfv
    #
    wceq
    #
    wph
    @1
    wa
    #
    cF
    @2
    cli
    wbr
    #
    cF
    @3
    cli
    wbr
    #
    @4
    @1
    @6
    wph
    @1
    @6
    cF
    climdm
    #
    biimpi
    adantl
    #
    @5
    cG
    @3
    cli
    wbr
    #
    @7
    @5
    cG
    @0
    wcel
    #
    @10
    @5
    @1
    @11
    @5
    @6
    @1
    @9
    @8
    sylibr
    wph
    @1
    @11
    wb
    #
    @1
    wph
    vk
    cF
    cG
    cM
    cV
    cW
    cZ
    climfveq.1
    climfveq.2
    climfveq.3
    climfveq.4
    climfveq.5
    climeldmeq
    #
    adantr
    mpbid
    cG
    climdm
    sylib
    @5
    @3
    vk
    cG
    cF
    cM
    cW
    cV
    cZ
    climfveq.1
    wph
    cG
    cW
    wcel
    @1
    climfveq.3
    adantr
    wph
    cF
    cV
    wcel
    @1
    climfveq.2
    adantr
    wph
    cM
    cz
    wcel
    @1
    climfveq.4
    adantr
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @14
    cG
    cfv
    #
    @14
    cF
    cfv
    #
    wceq
    @1
    wph
    @15
    wa
    @17
    @16
    climfveq.5
    eqcomd
    adantlr
    climeq
    mpbid
    @2
    @3
    cF
    climuni
    syl2anc
    wph
    @1
    wn
    #
    wa
    #
    @2
    c0
    @3
    @18
    @2
    c0
    wceq
    wph
    cF
    cli
    ndmfv
    adantl
    @19
    @11
    wn
    @3
    c0
    wceq
    @19
    @1
    @11
    wph
    @18
    simpr
    wph
    @12
    @18
    @13
    adantr
    mtbid
    cG
    cli
    ndmfv
    syl
    eqtr4d
    pm2.61dan
end
