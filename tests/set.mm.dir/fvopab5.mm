include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "cio.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "wbr.mm"
include "df-fv.mm"
include "breq2.mm"
include "nfcv.mm"
include "copab.mm"
include "nfopab2.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "nfv.mm"
include "cbviota.mm"
include "eqtri.mm"
include "wb.mm"
include "nfopab1.mm"
include "nfbi.mm"
include "breq1.mm"
include "bibi12d.mm"
include "cop.mm"
include "df-br.mm"
include "eleq2i.mm"
include "opabid.mm"
include "3bitri.mm"
include "vtoclg1f.mm"
include "iotabidv.mm"
include "syl5eq.mm"
include "syl.mm"

theorem fvopab5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cV: class V
  let vz: setvar z
  assume fvopab5.1: |- F = { <. x , y >. | ph }
  assume fvopab5.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F z
  assert |- ( A e. V -> ( F ` A ) = ( iota y ps ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cA
    cF
    cfv
    #
    wps
    vy
    cio
    #
    wceq
    cA
    cV
    elex
    @0
    @1
    cA
    vy
    cv
    #
    cF
    wbr
    #
    vy
    cio
    #
    @2
    @1
    cA
    vz
    cv
    #
    cF
    wbr
    #
    vz
    cio
    @5
    vz
    cA
    cF
    df-fv
    @7
    @4
    vz
    vy
    @6
    @3
    cA
    cF
    breq2
    vy
    cA
    @6
    cF
    vy
    cA
    nfcv
    vy
    cF
    wph
    vx
    vy
    copab
    #
    fvopab5.1
    wph
    vx
    vy
    nfopab2
    nfcxfr
    vy
    @6
    nfcv
    nfbr
    @4
    vz
    nfv
    cbviota
    eqtri
    @0
    @4
    wps
    vy
    vx
    cv
    #
    @3
    cF
    wbr
    #
    wph
    wb
    @4
    wps
    wb
    vx
    cA
    cvv
    @4
    wps
    vx
    vx
    cA
    @3
    cF
    vx
    cA
    nfcv
    vx
    cF
    @8
    fvopab5.1
    wph
    vx
    vy
    nfopab1
    nfcxfr
    vx
    @3
    nfcv
    nfbr
    wps
    vx
    nfv
    nfbi
    @9
    cA
    wceq
    @10
    @4
    wph
    wps
    @9
    cA
    @3
    cF
    breq1
    fvopab5.2
    bibi12d
    @10
    @9
    @3
    cop
    #
    cF
    wcel
    @11
    @8
    wcel
    wph
    @9
    @3
    cF
    df-br
    cF
    @8
    @11
    fvopab5.1
    eleq2i
    wph
    vx
    vy
    opabid
    3bitri
    vtoclg1f
    iotabidv
    syl5eq
    syl
end
