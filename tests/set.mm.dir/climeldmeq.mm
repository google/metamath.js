include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cvv.mm"
include "wbr.mm"
include "adantr.mm"
include "fvexd.mm"
include "wb.mm"
include "climdm.mm"
include "a1i.mm"
include "biimpa.mm"
include "climeq.mm"
include "mpbid.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "ex.mm"
include "biimpi.mm"
include "adantl.mm"
include "cv.mm"
include "eqcomd.mm"
include "impbid.mm"

theorem climeldmeq
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume climeldmeq.z: |- Z = ( ZZ>= ` M )
  assume climeldmeq.f: |- ( ph -> F e. V )
  assume climeldmeq.g: |- ( ph -> G e. W )
  assume climeldmeq.m: |- ( ph -> M e. ZZ )
  assume climeldmeq.e: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint Z k
  disjoint k ph
  assert |- ( ph -> ( F e. dom ~~> <-> G e. dom ~~> ) )

  proof
    wph
    cF
    cli
    cdm
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wph
    @1
    @2
    wph
    @1
    wa
    #
    cG
    cW
    wcel
    #
    cF
    cli
    cfv
    #
    cvv
    wcel
    cG
    @5
    cli
    wbr
    #
    @2
    wph
    @4
    @1
    climeldmeq.g
    adantr
    @3
    cF
    cli
    fvexd
    @3
    cF
    @5
    cli
    wbr
    #
    @6
    wph
    @1
    @7
    @1
    @7
    wb
    wph
    cF
    climdm
    a1i
    biimpa
    wph
    @7
    @6
    wb
    @1
    wph
    @5
    vk
    cF
    cG
    cM
    cV
    cW
    cZ
    climeldmeq.z
    climeldmeq.f
    climeldmeq.g
    climeldmeq.m
    climeldmeq.e
    climeq
    adantr
    mpbid
    cG
    @5
    cW
    cvv
    cli
    breldmg
    syl3anc
    ex
    wph
    @2
    @1
    wph
    @2
    wa
    #
    cF
    cV
    wcel
    #
    cG
    cli
    cfv
    #
    cvv
    wcel
    cF
    @10
    cli
    wbr
    #
    @1
    wph
    @9
    @2
    climeldmeq.f
    adantr
    @8
    cG
    cli
    fvexd
    @8
    cG
    @10
    cli
    wbr
    #
    @11
    @2
    @12
    wph
    @2
    @12
    cG
    climdm
    biimpi
    adantl
    wph
    @12
    @11
    wb
    @2
    wph
    @10
    vk
    cG
    cF
    cM
    cW
    cV
    cZ
    climeldmeq.z
    climeldmeq.g
    climeldmeq.f
    climeldmeq.m
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    @13
    cF
    cfv
    @13
    cG
    cfv
    climeldmeq.e
    eqcomd
    climeq
    adantr
    mpbid
    cF
    @10
    cV
    cvv
    cli
    breldmg
    syl3anc
    ex
    impbid
end
