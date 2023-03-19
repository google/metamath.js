include "corvc.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cuni.mm"
include "crab.mm"
include "cima.mm"
include "cr.mm"
include "cdm.mm"
include "cprb.mm"
include "wcel.mm"
include "csiga.mm"
include "domprobsiga.mm"
include "syl.mm"
include "ctop.mm"
include "retop.mm"
include "a1i.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "csigagen.mm"
include "crrv.mm"
include "rrvmbfm.mm"
include "mpbid.mm"
include "df-brsiga.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "orvcval4.mm"
include "wceq.mm"
include "uniretop.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "imaeq2i.mm"
include "syl6eqr.mm"

theorem orrvcval4
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

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint A z
  disjoint R z
  disjoint X z
  assert |- ( ph -> ( X oRVC R A ) = ( `' X " { y e. RR | y R A } ) )

  proof
    wph
    cX
    cA
    cR
    corvc
    co
    cX
    ccnv
    #
    vy
    cv
    cA
    cR
    wbr
    #
    vy
    cioo
    crn
    ctg
    cfv
    #
    cuni
    #
    crab
    #
    cima
    @0
    @1
    vy
    cr
    crab
    #
    cima
    wph
    vy
    cA
    cR
    cP
    cdm
    #
    @2
    cV
    cX
    wph
    cP
    cprb
    wcel
    @6
    csiga
    crn
    cuni
    wcel
    orrvccel.1
    cP
    domprobsiga
    syl
    @2
    ctop
    wcel
    wph
    retop
    a1i
    wph
    cX
    @6
    cbrsiga
    cmbfm
    co
    #
    @6
    @2
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
    @7
    wcel
    orrvccel.2
    wph
    cP
    cX
    orrvccel.1
    rrvmbfm
    mpbid
    cbrsiga
    @8
    @6
    cmbfm
    df-brsiga
    oveq2i
    syl6eleq
    orrvccel.4
    orvcval4
    @5
    @4
    @0
    cr
    @3
    wceq
    @5
    @4
    wceq
    uniretop
    @1
    vy
    cr
    @3
    rabeq
    ax-mp
    imaeq2i
    syl6eqr
end
