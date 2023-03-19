include "cif.mm"
include "ifeq12da.mm"
include "ifbid.mm"
include "eqtrd.mm"

theorem ifbieq12d2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifbieq12d2.1: |- ( ph -> ( ps <-> ch ) )
  assume ifbieq12d2.2: |- ( ( ph /\ ps ) -> A = C )
  assume ifbieq12d2.3: |- ( ( ph /\ -. ps ) -> B = D )


  assert |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) )

  proof
    wph
    wps
    cA
    cB
    cif
    wps
    cC
    cD
    cif
    wch
    cC
    cD
    cif
    wph
    wps
    cA
    cB
    cC
    cD
    ifbieq12d2.2
    ifbieq12d2.3
    ifeq12da
    wph
    wps
    wch
    cC
    cD
    ifbieq12d2.1
    ifbid
    eqtrd
end
