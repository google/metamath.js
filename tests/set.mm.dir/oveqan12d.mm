include "wceq.mm"
include "co.mm"
include "oveq12.mm"
include "syl2an.mm"

theorem oveqan12d
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  param cF: class F
  assume oveq1d.1: |- ( ph -> A = B )
  assume opreqan12i.2: |- ( ps -> C = D )


  assert |- ( ( ph /\ ps ) -> ( A F C ) = ( B F D ) )

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
    cF
    co
    cB
    cD
    cF
    co
    wceq
    wps
    oveq1d.1
    opreqan12i.2
    cA
    cB
    cC
    cD
    cF
    oveq12
    syl2an
end
