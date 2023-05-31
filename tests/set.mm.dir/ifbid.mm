include "wb.mm"
include "cif.mm"
include "wceq.mm"
include "ifbi.mm"
include "syl.mm"

theorem ifbid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param cA: class A
  param cB: class B
  assume ifbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> if ( ps , A , B ) = if ( ch , A , B ) )

  proof
    wph
    wps
    wch
    wb
    wps
    cA
    cB
    cif
    wch
    cA
    cB
    cif
    wceq
    ifbid.1
    wps
    wch
    cA
    cB
    ifbi
    syl
end
