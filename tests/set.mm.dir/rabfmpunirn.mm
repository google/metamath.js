include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "cab.mm"
include "df-rab.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "zfausab.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "abfmpunirn.mm"
include "elex.mm"
include "adantr.mm"
include "rexlimivw.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"

theorem rabfmpunirn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  assume rabfmpunirn.1: |- F = ( x e. V |-> { y e. W | ph } )
  assume rabfmpunirn.2: |- W e. _V
  assume rabfmpunirn.3: |- ( y = B -> ( ph <-> ps ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint W y
  disjoint ps y
  assert |- ( B e. U. ran F <-> E. x e. V ( B e. W /\ ps ) )

  proof
    cB
    cF
    crn
    cuni
    wcel
    cB
    cvv
    wcel
    #
    cB
    cW
    wcel
    #
    wps
    wa
    #
    vx
    cV
    wrex
    #
    wa
    @3
    vy
    cv
    #
    cW
    wcel
    #
    wph
    wa
    #
    @2
    vx
    vy
    cB
    cF
    cV
    cF
    vx
    cV
    wph
    vy
    cW
    crab
    #
    cmpt
    vx
    cV
    @6
    vy
    cab
    #
    cmpt
    rabfmpunirn.1
    vx
    cV
    @7
    @8
    wph
    vy
    cW
    df-rab
    mpteq2i
    eqtri
    wph
    vy
    cW
    rabfmpunirn.2
    zfausab
    @4
    cB
    wceq
    @5
    @1
    wph
    wps
    @4
    cB
    cW
    eleq1
    rabfmpunirn.3
    anbi12d
    abfmpunirn
    @3
    @0
    @2
    @0
    vx
    cV
    @1
    @0
    wps
    cB
    cW
    elex
    adantr
    rexlimivw
    pm4.71ri
    bitr4i
end
