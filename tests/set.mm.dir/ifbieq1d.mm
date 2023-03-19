include "cif.mm"
include "ifbid.mm"
include "ifeq1d.mm"
include "eqtrd.mm"

theorem ifbieq1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param cA: class A
  param cB: class B
  param cC: class C
  assume ifbieq1d.1: |- ( ph -> ( ps <-> ch ) )
  assume ifbieq1d.2: |- ( ph -> A = B )


  assert |- ( ph -> if ( ps , A , C ) = if ( ch , B , C ) )

  proof
    wph
    wps
    cA
    cC
    cif
    wch
    cA
    cC
    cif
    wch
    cB
    cC
    cif
    wph
    wps
    wch
    cA
    cC
    ifbieq1d.1
    ifbid
    wph
    wch
    cA
    cB
    cC
    ifbieq1d.2
    ifeq1d
    eqtrd
end
