include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "clsi.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "climliminflimsup2.mm"
include "liminfgelimsupuz.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem climliminflimsup4
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminflimsup4.1: |- ( ph -> M e. ZZ )
  assume climliminflimsup4.2: |- Z = ( ZZ>= ` M )
  assume climliminflimsup4.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> ( ( limsup ` F ) e. RR /\ ( liminf ` F ) = ( limsup ` F ) ) ) )

  proof
    wph
    cF
    cli
    cdm
    wcel
    cF
    clsp
    cfv
    #
    cr
    wcel
    #
    @0
    cF
    clsi
    cfv
    #
    cle
    wbr
    #
    wa
    @1
    @2
    @0
    wceq
    #
    wa
    wph
    cF
    cM
    cZ
    climliminflimsup4.1
    climliminflimsup4.2
    climliminflimsup4.3
    climliminflimsup2
    wph
    @3
    @4
    @1
    wph
    cF
    cM
    cZ
    climliminflimsup4.1
    climliminflimsup4.2
    climliminflimsup4.3
    liminfgelimsupuz
    anbi2d
    bitrd
end
