include "wa.mm"
include "wn.mm"
include "w3a.mm"
include "wo.mm"
include "wcad.mm"
include "ianor.mm"
include "3anbi123i.mm"
include "w3o.mm"
include "3ioran.mm"
include "cador.mm"
include "xchnxbir.mm"
include "cadan.mm"
include "3bitr4i.mm"

theorem cadnot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. cadd ( ph , ps , ch ) <-> cadd ( -. ph , -. ps , -. ch ) )

  proof
    wph
    wps
    wa
    #
    wn
    #
    wph
    wch
    wa
    #
    wn
    #
    wps
    wch
    wa
    #
    wn
    #
    w3a
    #
    wph
    wn
    #
    wps
    wn
    #
    wo
    #
    @7
    wch
    wn
    #
    wo
    #
    @8
    @10
    wo
    #
    w3a
    wph
    wps
    wch
    wcad
    #
    wn
    @7
    @8
    @10
    wcad
    @1
    @9
    @3
    @11
    @5
    @12
    wph
    wps
    ianor
    wph
    wch
    ianor
    wps
    wch
    ianor
    3anbi123i
    @0
    @2
    @4
    w3o
    @6
    @13
    @0
    @2
    @4
    3ioran
    wph
    wps
    wch
    cador
    xchnxbir
    @7
    @8
    @10
    cadan
    3bitr4i
end
