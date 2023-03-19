include "wbr.mm"
include "wb.mm"
include "breqan12d.mm"
include "ancoms.mm"

theorem breqan12rd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume breq1d.1: |- ( ph -> A = B )
  assume breqan12i.2: |- ( ps -> C = D )


  assert |- ( ( ps /\ ph ) -> ( A R C <-> B R D ) )

  proof
    wph
    wps
    cA
    cC
    cR
    wbr
    cB
    cD
    cR
    wbr
    wb
    wph
    wps
    cA
    cB
    cC
    cD
    cR
    breq1d.1
    breqan12i.2
    breqan12d
    ancoms
end
