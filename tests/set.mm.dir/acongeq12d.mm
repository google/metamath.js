include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "negeqd.mm"
include "orbi12d.mm"

theorem acongeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume acongeq12d.1: |- ( ph -> B = C )
  assume acongeq12d.2: |- ( ph -> D = E )


  assert |- ( ph -> ( ( A || ( B - D ) \/ A || ( B - -u D ) ) <-> ( A || ( C - E ) \/ A || ( C - -u E ) ) ) )

  proof
    wph
    cA
    cB
    cD
    cmin
    co
    #
    cdvds
    wbr
    cA
    cC
    cE
    cmin
    co
    #
    cdvds
    wbr
    cA
    cB
    cD
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    cA
    cC
    cE
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    wph
    @0
    @1
    cA
    cdvds
    wph
    cB
    cC
    cD
    cE
    cmin
    acongeq12d.1
    acongeq12d.2
    oveq12d
    breq2d
    wph
    @3
    @5
    cA
    cdvds
    wph
    cB
    cC
    @2
    @4
    cmin
    acongeq12d.1
    wph
    cD
    cE
    acongeq12d.2
    negeqd
    oveq12d
    breq2d
    orbi12d
end
