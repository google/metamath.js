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
include "cz.mm"
include "adantr.mm"
include "climliminf.mm"
include "biimpd.mm"
include "imp.mm"
include "cv.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "climrecl.mm"
include "simpr.mm"
include "limsupcld.mm"
include "climliminflimsupd.mm"
include "eqcomd.mm"
include "xreqled.mm"
include "jca.mm"
include "simprl.mm"
include "simprr.mm"
include "liminflimsupclim.mm"
include "impbida.mm"

theorem climliminflimsup
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminflimsup.1: |- ( ph -> M e. ZZ )
  assume climliminflimsup.2: |- Z = ( ZZ>= ` M )
  assume climliminflimsup.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> ( ( liminf ` F ) e. RR /\ ( limsup ` F ) <_ ( liminf ` F ) ) ) )

  proof
    wph
    cF
    cli
    cdm
    #
    wcel
    #
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
    @2
    cle
    wbr
    #
    wa
    #
    wph
    @1
    wa
    #
    @3
    @5
    @7
    @2
    vk
    cF
    cM
    cZ
    climliminflimsup.2
    wph
    cM
    cz
    wcel
    #
    @1
    climliminflimsup.1
    adantr
    #
    wph
    @1
    cF
    @2
    cli
    wbr
    #
    wph
    @1
    @10
    wph
    cF
    cM
    cZ
    climliminflimsup.1
    climliminflimsup.2
    climliminflimsup.3
    climliminf
    biimpd
    imp
    @7
    cZ
    cr
    vk
    cv
    cF
    wph
    cZ
    cr
    cF
    wf
    #
    @1
    climliminflimsup.3
    adantr
    #
    ffvelrnda
    climrecl
    @7
    @4
    @2
    @7
    cF
    @0
    wph
    @1
    simpr
    #
    limsupcld
    @7
    @2
    @4
    @7
    cF
    cM
    cZ
    @9
    climliminflimsup.2
    @12
    @13
    climliminflimsupd
    eqcomd
    xreqled
    jca
    wph
    @6
    wa
    cF
    cM
    cZ
    wph
    @8
    @6
    climliminflimsup.1
    adantr
    climliminflimsup.2
    wph
    @11
    @6
    climliminflimsup.3
    adantr
    wph
    @3
    @5
    simprl
    wph
    @3
    @5
    simprr
    liminflimsupclim
    impbida
end
