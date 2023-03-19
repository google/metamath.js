include "cdm.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cprb.mm"
include "wcel.mm"
include "csiga.mm"
include "cuni.mm"
include "domprobsiga.mm"
include "syl.mm"
include "ctop.mm"
include "retop.mm"
include "a1i.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "csigagen.mm"
include "crrv.mm"
include "rrvmbfm.mm"
include "mpbid.mm"
include "df-brsiga.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "ccld.mm"
include "wceq.mm"
include "uniretop.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "syl5eqelr.mm"
include "orvccel.mm"

theorem orrvccel
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cR: class R
  let cV: class V
  let cX: class X
  let vz: setvar z
  assume orrvccel.1: |- ( ph -> P e. Prob )
  assume orrvccel.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orrvccel.4: |- ( ph -> A e. V )
  assume orrvccel.5: |- ( ph -> { y e. RR | y R A } e. ( Clsd ` ( topGen ` ran (,) ) ) )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint A z
  disjoint R z
  disjoint X z
  assert |- ( ph -> ( X oRVC R A ) e. dom P )

  proof
    wph
    vy
    cA
    cR
    cP
    cdm
    #
    cioo
    crn
    ctg
    cfv
    #
    cV
    cX
    wph
    cP
    cprb
    wcel
    @0
    csiga
    crn
    cuni
    wcel
    orrvccel.1
    cP
    domprobsiga
    syl
    @1
    ctop
    wcel
    wph
    retop
    a1i
    wph
    cX
    @0
    cbrsiga
    cmbfm
    co
    #
    @0
    @1
    csigagen
    cfv
    #
    cmbfm
    co
    wph
    cX
    cP
    crrv
    cfv
    wcel
    cX
    @2
    wcel
    orrvccel.2
    wph
    cP
    cX
    orrvccel.1
    rrvmbfm
    mpbid
    cbrsiga
    @3
    @0
    cmbfm
    df-brsiga
    oveq2i
    syl6eleq
    orrvccel.4
    wph
    vy
    cv
    cA
    cR
    wbr
    #
    vy
    @1
    cuni
    #
    crab
    #
    @4
    vy
    cr
    crab
    #
    @1
    ccld
    cfv
    cr
    @5
    wceq
    @7
    @6
    wceq
    uniretop
    @4
    vy
    cr
    @5
    rabeq
    ax-mp
    orrvccel.5
    syl5eqelr
    orvccel
end
