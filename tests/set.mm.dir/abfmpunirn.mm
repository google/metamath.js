include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "wrex.mm"
include "elex.mm"
include "cab.mm"
include "cv.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "fnmpti.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "wceq.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "eleq2d.mm"
include "rexbiia.mm"
include "bitri.mm"
include "elabg.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "biadan2.mm"

theorem abfmpunirn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cV: class V
  assume abfmpunirn.1: |- F = ( x e. V |-> { y | ph } )
  assume abfmpunirn.2: |- { y | ph } e. _V
  assume abfmpunirn.3: |- ( y = B -> ( ph <-> ps ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint ps y
  assert |- ( B e. U. ran F <-> ( B e. _V /\ E. x e. V ps ) )

  proof
    cB
    cF
    crn
    cuni
    #
    wcel
    #
    cB
    cvv
    wcel
    #
    wps
    vx
    cV
    wrex
    #
    cB
    @0
    elex
    @1
    cB
    wph
    vy
    cab
    #
    wcel
    #
    vx
    cV
    wrex
    #
    @2
    @3
    @1
    cB
    vx
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vx
    cV
    wrex
    #
    @6
    cF
    cV
    wfn
    @1
    @10
    wb
    vx
    cV
    @4
    cF
    abfmpunirn.2
    abfmpunirn.1
    fnmpti
    vx
    cB
    cF
    cV
    fnunirn
    ax-mp
    @9
    @5
    vx
    cV
    @7
    cV
    wcel
    #
    @8
    @4
    cB
    @11
    @4
    cvv
    wcel
    @8
    @4
    wceq
    abfmpunirn.2
    vx
    cV
    @4
    cvv
    cF
    abfmpunirn.1
    fvmpt2
    mpan2
    eleq2d
    rexbiia
    bitri
    @2
    @5
    wps
    vx
    cV
    wph
    wps
    vy
    cB
    cvv
    abfmpunirn.3
    elabg
    rexbidv
    syl5bb
    biadan2
end
