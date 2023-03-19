include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "syl.mm"
include "wn.mm"
include "iffalse.mm"
include "cases.mm"

theorem elimif
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let cA: class A
  let cB: class B
  assume elimif.1: |- ( if ( ph , A , B ) = A -> ( ps <-> ch ) )
  assume elimif.2: |- ( if ( ph , A , B ) = B -> ( ps <-> th ) )


  assert |- ( ps <-> ( ( ph /\ ch ) \/ ( -. ph /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wph
    cA
    cB
    cif
    #
    cA
    wceq
    wps
    wch
    wb
    wph
    cA
    cB
    iftrue
    elimif.1
    syl
    wph
    wn
    @0
    cB
    wceq
    wps
    wth
    wb
    wph
    cA
    cB
    iffalse
    elimif.2
    syl
    cases
end
