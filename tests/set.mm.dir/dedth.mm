include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "mpbiri.mm"

theorem dedth
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  assume dedth.1: |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) )
  assume dedth.2: |- ch


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    dedth.2
    wph
    cA
    wph
    cA
    cB
    cif
    #
    wceq
    wps
    wch
    wb
    wph
    @0
    cA
    wph
    cA
    cB
    iftrue
    eqcomd
    dedth.1
    syl
    mpbiri
end
