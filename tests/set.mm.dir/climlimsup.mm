include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "clsp.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "cz.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "simpr.mm"
include "climcau.mm"
include "syl2anc.mm"
include "caurcvg.mm"
include "wrel.mm"
include "climrel.mm"
include "releldm.mm"
include "mpan.mm"
include "adantl.mm"
include "impbida.mm"

theorem climlimsup
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  assume climlimsup.1: |- ( ph -> M e. ZZ )
  assume climlimsup.2: |- Z = ( ZZ>= ` M )
  assume climlimsup.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> F ~~> ( limsup ` F ) ) )

  proof
    wph
    cF
    cli
    cdm
    wcel
    #
    cF
    cF
    clsp
    cfv
    #
    cli
    wbr
    #
    wph
    @0
    wa
    #
    vx
    vk
    vm
    cF
    cM
    cZ
    climlimsup.2
    wph
    cZ
    cr
    cF
    wf
    @0
    climlimsup.3
    adantr
    @3
    cM
    cz
    wcel
    #
    @0
    vk
    cv
    cF
    cfv
    vm
    cv
    #
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    vk
    @5
    cuz
    cfv
    wral
    vm
    cZ
    wrex
    vx
    crp
    wral
    wph
    @4
    @0
    climlimsup.1
    adantr
    wph
    @0
    simpr
    vx
    vm
    vk
    cF
    cM
    cZ
    climlimsup.2
    climcau
    syl2anc
    caurcvg
    @2
    @0
    wph
    cli
    wrel
    @2
    @0
    climrel
    cF
    @1
    cli
    releldm
    mpan
    adantl
    impbida
end
