include "cv.mm"
include "wsbc.mm"
include "cif.mm"
include "dfsbcq.mm"
include "wb.mm"
include "wceq.mm"
include "sbcid.mm"
include "ifbi.mm"
include "mp2b.mm"
include "mpbir.mm"
include "dedth.mm"
include "3imtr3i.mm"

theorem dedths
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cB: class B
  assume dedths.1: |- [. if ( ph , x , B ) / x ]. ps


  assert |- ( ph -> ps )

  proof
    wph
    vx
    vx
    cv
    #
    wsbc
    #
    wps
    vx
    @0
    wsbc
    #
    wph
    wps
    @1
    @2
    wps
    vx
    @1
    @0
    cB
    cif
    #
    wsbc
    #
    @0
    cB
    wps
    vx
    @0
    @3
    dfsbcq
    @4
    wps
    vx
    wph
    @0
    cB
    cif
    #
    wsbc
    #
    dedths.1
    @1
    wph
    wb
    @3
    @5
    wceq
    @4
    @6
    wb
    wph
    vx
    sbcid
    #
    @1
    wph
    @0
    cB
    ifbi
    wps
    vx
    @3
    @5
    dfsbcq
    mp2b
    mpbir
    dedth
    @7
    wps
    vx
    sbcid
    3imtr3i
end
