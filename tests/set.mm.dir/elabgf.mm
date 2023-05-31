include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wb.mm"
include "nfab1.mm"
include "nfel.mm"
include "nfbi.mm"
include "wceq.mm"
include "eleq1.mm"
include "bibi12d.mm"
include "abid.mm"
include "vtoclgf.mm"

theorem elabgf
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume elabgf.1: |- F/_ x A
  assume elabgf.2: |- F/ x ps
  assume elabgf.3: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( A e. B -> ( A e. { x | ph } <-> ps ) )

  proof
    vx
    cv
    #
    wph
    vx
    cab
    #
    wcel
    #
    wph
    wb
    cA
    @1
    wcel
    #
    wps
    wb
    vx
    cA
    cB
    elabgf.1
    @3
    wps
    vx
    vx
    cA
    @1
    elabgf.1
    wph
    vx
    nfab1
    nfel
    elabgf.2
    nfbi
    @0
    cA
    wceq
    @2
    @3
    wph
    wps
    @0
    cA
    @1
    eleq1
    elabgf.3
    bibi12d
    wph
    vx
    abid
    vtoclgf
end
