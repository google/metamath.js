include "cif.mm"
include "ifbid.mm"
include "ifeq1d.mm"
include "eqtrd.mm"

theorem ifbieq1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
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
