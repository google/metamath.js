include "wb.mm"
include "w3a.mm"
include "w3o.mm"
include "wo.mm"
include "idn1.mm"
include "simp1.mm"
include "e1a.mm"
include "simp2.mm"
include "pm4.39.mm"
include "ex.mm"
include "e11.mm"
include "simp3.mm"
include "df-3or.mm"
include "bicomi.mm"
include "bitr3.mm"
include "com12.mm"
include "e10.mm"
include "bitr.mm"
include "in1.mm"

theorem 3orbi123VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) ) -> ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wta
    wet
    wb
    #
    w3a
    #
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
    wb
    #
    @3
    @4
    wps
    wth
    wo
    #
    wet
    wo
    #
    wb
    #
    @8
    @5
    wb
    #
    @6
    @3
    wph
    wch
    wo
    #
    wta
    wo
    #
    @8
    wb
    #
    @12
    @4
    wb
    #
    @9
    @3
    @11
    @7
    wb
    #
    @2
    @13
    @3
    @0
    @1
    @15
    @3
    @3
    @0
    @3
    idn1
    #
    @0
    @1
    @2
    simp1
    e1a
    @3
    @3
    @1
    @16
    @0
    @1
    @2
    simp2
    e1a
    @0
    @1
    @15
    wph
    wch
    wps
    wth
    pm4.39
    ex
    e11
    @3
    @3
    @2
    @16
    @0
    @1
    @2
    simp3
    e1a
    @15
    @2
    @13
    @11
    wta
    @7
    wet
    pm4.39
    ex
    e11
    @4
    @12
    wph
    wch
    wta
    df-3or
    bicomi
    @14
    @13
    @9
    @12
    @4
    @8
    bitr3
    com12
    e10
    @5
    @8
    wps
    wth
    wet
    df-3or
    bicomi
    @9
    @10
    @6
    @4
    @8
    @5
    bitr
    ex
    e10
    in1
end
