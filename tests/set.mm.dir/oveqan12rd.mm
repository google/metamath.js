include "co.mm"
include "wceq.mm"
include "oveqan12d.mm"
include "ancoms.mm"

theorem oveqan12rd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume oveq1d.1: |- ( ph -> A = B )
  assume opreqan12i.2: |- ( ps -> C = D )


  assert |- ( ( ps /\ ph ) -> ( A F C ) = ( B F D ) )

  proof
    wph
    wps
    cA
    cC
    cF
    co
    cB
    cD
    cF
    co
    wceq
    wph
    wps
    cA
    cB
    cC
    cD
    cF
    oveq1d.1
    opreqan12i.2
    oveqan12d
    ancoms
end
