include "wb.mm"
include "wn.mm"
include "whad.mm"
include "notbi.mm"
include "bibi1i.mm"
include "xor3.mm"
include "hadbi.mm"
include "xchnxbir.mm"
include "3bitr4i.mm"

theorem hadnot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. hadd ( ph , ps , ch ) <-> hadd ( -. ph , -. ps , -. ch ) )

  proof
    wph
    wps
    wb
    #
    wch
    wn
    #
    wb
    #
    wph
    wn
    #
    wps
    wn
    #
    wb
    #
    @1
    wb
    wph
    wps
    wch
    whad
    #
    wn
    @3
    @4
    @1
    whad
    @0
    @5
    @1
    wph
    wps
    notbi
    bibi1i
    @0
    wch
    wb
    @2
    @6
    @0
    wch
    xor3
    wph
    wps
    wch
    hadbi
    xchnxbir
    @3
    @4
    @1
    hadbi
    3bitr4i
end
