include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq12.mm"
include "syl2an.mm"

theorem breqan12d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume breq1d.1: |- ( ph -> A = B )
  assume breqan12i.2: |- ( ps -> C = D )


  assert |- ( ( ph /\ ps ) -> ( A R C <-> B R D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cR
    wbr
    cB
    cD
    cR
    wbr
    wb
    wps
    breq1d.1
    breqan12i.2
    cA
    cB
    cC
    cD
    cR
    breq12
    syl2an
end
