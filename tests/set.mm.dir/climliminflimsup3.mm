include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "clsi.mm"
include "cfv.mm"
include "cr.mm"
include "clsp.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "climliminflimsup.mm"
include "liminfgelimsupuz.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem climliminflimsup3
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminflimsup3.1: |- ( ph -> M e. ZZ )
  assume climliminflimsup3.2: |- Z = ( ZZ>= ` M )
  assume climliminflimsup3.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> ( ( liminf ` F ) e. RR /\ ( liminf ` F ) = ( limsup ` F ) ) ) )

  proof
    wph
    cF
    cli
    cdm
    wcel
    cF
    clsi
    cfv
    #
    cr
    wcel
    #
    cF
    clsp
    cfv
    #
    @0
    cle
    wbr
    #
    wa
    @1
    @0
    @2
    wceq
    #
    wa
    wph
    cF
    cM
    cZ
    climliminflimsup3.1
    climliminflimsup3.2
    climliminflimsup3.3
    climliminflimsup
    wph
    @3
    @4
    @1
    wph
    cF
    cM
    cZ
    climliminflimsup3.1
    climliminflimsup3.2
    climliminflimsup3.3
    liminfgelimsupuz
    anbi2d
    bitrd
end
