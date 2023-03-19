include "cif.mm"
include "ifbid.mm"
include "ifeq12d.mm"
include "eqtrd.mm"

theorem ifbieq12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifbieq12d.1: |- ( ph -> ( ps <-> ch ) )
  assume ifbieq12d.2: |- ( ph -> A = C )
  assume ifbieq12d.3: |- ( ph -> B = D )


  assert |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) )

  proof
    wph
    wps
    cA
    cB
    cif
    wch
    cA
    cB
    cif
    wch
    cC
    cD
    cif
    wph
    wps
    wch
    cA
    cB
    ifbieq12d.1
    ifbid
    wph
    wch
    cA
    cC
    cB
    cD
    ifbieq12d.2
    ifbieq12d.3
    ifeq12d
    eqtrd
end
