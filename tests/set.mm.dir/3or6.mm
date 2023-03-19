include "wo.mm"
include "w3o.mm"
include "or4.mm"
include "orbi1i.mm"
include "bitr2i.mm"
include "df-3or.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem 3or6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <-> ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) )

  proof
    wph
    wps
    wo
    #
    wch
    wth
    wo
    #
    wo
    #
    wta
    wet
    wo
    #
    wo
    #
    wph
    wch
    wo
    #
    wta
    wo
    #
    wps
    wth
    wo
    #
    wet
    wo
    #
    wo
    #
    @0
    @1
    @3
    w3o
    wph
    wch
    wta
    w3o
    #
    wps
    wth
    wet
    w3o
    #
    wo
    @9
    @5
    @7
    wo
    #
    @3
    wo
    @4
    @5
    wta
    @7
    wet
    or4
    @12
    @2
    @3
    wph
    wch
    wps
    wth
    or4
    orbi1i
    bitr2i
    @0
    @1
    @3
    df-3or
    @10
    @6
    @11
    @8
    wph
    wch
    wta
    df-3or
    wps
    wth
    wet
    df-3or
    orbi12i
    3bitr4i
end
