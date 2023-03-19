include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "clsi.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "clsp.mm"
include "climlimsup.mm"
include "biimpd.mm"
include "imp.mm"
include "cz.mm"
include "adantr.mm"
include "cr.mm"
include "wf.mm"
include "simpr.mm"
include "climliminflimsupd.mm"
include "breqtrrd.mm"
include "climrel.mm"
include "releldmi.mm"
include "adantl.mm"
include "impbida.mm"

theorem climliminf
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminf.1: |- ( ph -> M e. ZZ )
  assume climliminf.2: |- Z = ( ZZ>= ` M )
  assume climliminf.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> F ~~> ( liminf ` F ) ) )

  proof
    wph
    cF
    cli
    cdm
    wcel
    #
    cF
    cF
    clsi
    cfv
    #
    cli
    wbr
    #
    wph
    @0
    wa
    #
    cF
    cF
    clsp
    cfv
    #
    @1
    cli
    wph
    @0
    cF
    @4
    cli
    wbr
    #
    wph
    @0
    @5
    wph
    cF
    cM
    cZ
    climliminf.1
    climliminf.2
    climliminf.3
    climlimsup
    biimpd
    imp
    @3
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    @0
    climliminf.1
    adantr
    climliminf.2
    wph
    cZ
    cr
    cF
    wf
    @0
    climliminf.3
    adantr
    wph
    @0
    simpr
    climliminflimsupd
    breqtrrd
    @2
    @0
    wph
    cF
    @1
    cli
    climrel
    releldmi
    adantl
    impbida
end
