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
include "climliminflimsup.mm"
include "wceq.mm"
include "cz.mm"
include "adantr.mm"
include "wf.mm"
include "simprl.mm"
include "simprr.mm"
include "liminflimsupclim.mm"
include "simpr.mm"
include "climliminflimsupd.mm"
include "eqcomd.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "jca.mm"
include "liminfgelimsupuz.mm"
include "mpbid.mm"
include "adantrl.mm"
include "impbida.mm"
include "bitrd.mm"

theorem climliminflimsup2
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminflimsup2.1: |- ( ph -> M e. ZZ )
  assume climliminflimsup2.2: |- Z = ( ZZ>= ` M )
  assume climliminflimsup2.3: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F e. dom ~~> <-> ( ( limsup ` F ) e. RR /\ ( limsup ` F ) <_ ( liminf ` F ) ) ) )

  proof
    wph
    cF
    cli
    cdm
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
    @1
    cle
    wbr
    #
    wa
    #
    @3
    cr
    wcel
    #
    @4
    wa
    #
    wph
    cF
    cM
    cZ
    climliminflimsup2.1
    climliminflimsup2.2
    climliminflimsup2.3
    climliminflimsup
    wph
    @5
    @7
    wph
    @5
    wa
    #
    @6
    @4
    @8
    @3
    @1
    cr
    wph
    @5
    @0
    @3
    @1
    wceq
    @8
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    #
    @5
    climliminflimsup2.1
    adantr
    climliminflimsup2.2
    wph
    cZ
    cr
    cF
    wf
    #
    @5
    climliminflimsup2.3
    adantr
    wph
    @2
    @4
    simprl
    #
    wph
    @2
    @4
    simprr
    #
    liminflimsupclim
    wph
    @0
    wa
    #
    @1
    @3
    @13
    cF
    cM
    cZ
    wph
    @9
    @0
    climliminflimsup2.1
    adantr
    climliminflimsup2.2
    wph
    @10
    @0
    climliminflimsup2.3
    adantr
    wph
    @0
    simpr
    climliminflimsupd
    eqcomd
    syldan
    @11
    eqeltrd
    @12
    jca
    wph
    @7
    wa
    #
    @2
    @4
    @14
    @1
    @3
    cr
    wph
    @4
    @1
    @3
    wceq
    #
    @6
    wph
    @4
    wa
    #
    @4
    @15
    wph
    @4
    simpr
    @16
    cF
    cM
    cZ
    wph
    @9
    @4
    climliminflimsup2.1
    adantr
    climliminflimsup2.2
    wph
    @10
    @4
    climliminflimsup2.3
    adantr
    liminfgelimsupuz
    mpbid
    adantrl
    wph
    @6
    @4
    simprl
    eqeltrd
    wph
    @6
    @4
    simprr
    jca
    impbida
    bitrd
end
