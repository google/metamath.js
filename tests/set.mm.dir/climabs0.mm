include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cc0.mm"
include "cli.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "uztrn2.mm"
include "cc.mm"
include "wceq.mm"
include "absidm.mm"
include "syl.mm"
include "breq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "abscld.mm"
include "recnd.mm"
include "clim0c.mm"
include "eqidd.mm"
include "3bitr4rd.mm"

theorem climabs0
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume climabs0.1: |- Z = ( ZZ>= ` M )
  assume climabs0.2: |- ( ph -> M e. ZZ )
  assume climabs0.3: |- ( ph -> F e. V )
  assume climabs0.4: |- ( ph -> G e. W )
  assume climabs0.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climabs0.6: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( abs ` ( F ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F x
  disjoint G j
  disjoint G x
  disjoint M j
  disjoint j ph
  disjoint ph x
  disjoint Z j
  assert |- ( ph -> ( F ~~> 0 <-> G ~~> 0 ) )

  proof
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @2
    @4
    clt
    wbr
    #
    vk
    @7
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    cG
    cc0
    cli
    wbr
    cF
    cc0
    cli
    wbr
    wph
    @9
    @12
    vx
    crp
    wph
    @8
    @11
    vj
    cZ
    wph
    @6
    cZ
    wcel
    #
    wa
    @5
    @10
    vk
    @7
    wph
    @13
    @0
    @7
    wcel
    #
    @5
    @10
    wb
    #
    @13
    @14
    wa
    wph
    @0
    cZ
    wcel
    #
    @15
    cM
    @0
    @6
    cZ
    climabs0.1
    uztrn2
    wph
    @16
    wa
    #
    @3
    @2
    @4
    clt
    @17
    @1
    cc
    wcel
    @3
    @2
    wceq
    climabs0.5
    @1
    absidm
    syl
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    wph
    vx
    @2
    vj
    vk
    cG
    cM
    cW
    cZ
    climabs0.1
    climabs0.2
    climabs0.4
    climabs0.6
    @17
    @2
    @17
    @1
    climabs0.5
    abscld
    recnd
    clim0c
    wph
    vx
    @1
    vj
    vk
    cF
    cM
    cV
    cZ
    climabs0.1
    climabs0.2
    climabs0.3
    @17
    @1
    eqidd
    climabs0.5
    clim0c
    3bitr4rd
end
