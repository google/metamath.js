include "ccnv.mm"
include "csup.mm"
include "cinf.mm"
include "cnveqd.mm"
include "supeq123d.mm"
include "df-inf.mm"
include "3eqtr4g.mm"

theorem infeq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume infeq123d.a: |- ( ph -> A = D )
  assume infeq123d.b: |- ( ph -> B = E )
  assume infeq123d.c: |- ( ph -> C = F )


  assert |- ( ph -> inf ( A , B , C ) = inf ( D , E , F ) )

  proof
    wph
    cA
    cB
    cC
    ccnv
    #
    csup
    cD
    cE
    cF
    ccnv
    #
    csup
    cA
    cB
    cC
    cinf
    cD
    cE
    cF
    cinf
    wph
    cA
    cB
    @0
    cD
    cE
    @1
    infeq123d.a
    infeq123d.b
    wph
    cC
    cF
    infeq123d.c
    cnveqd
    supeq123d
    cA
    cB
    cC
    df-inf
    cD
    cE
    cF
    df-inf
    3eqtr4g
end
