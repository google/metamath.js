include "cs5.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs6.mm"
include "s5eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s6.mm"
include "3eqtr4g.mm"

theorem s6eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )
  assume s4eqd.4: |- ( ph -> D = Q )
  assume s5eqd.5: |- ( ph -> E = R )
  assume s6eqd.6: |- ( ph -> F = S )


  assert |- ( ph -> <" A B C D E F "> = <" N O P Q R S "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cE
    cs5
    #
    cF
    cs1
    #
    cconcat
    co
    cN
    cO
    cP
    cQ
    cR
    cs5
    #
    cS
    cs1
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cN
    cO
    cP
    cQ
    cR
    cS
    cs6
    wph
    @0
    @2
    @1
    @3
    cconcat
    wph
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cE
    cN
    cO
    s2eqd.1
    s2eqd.2
    s3eqd.3
    s4eqd.4
    s5eqd.5
    s5eqd
    wph
    cF
    cS
    s6eqd.6
    s1eqd
    oveq12d
    cA
    cB
    cC
    cD
    cE
    cF
    df-s6
    cN
    cO
    cP
    cQ
    cR
    cS
    df-s6
    3eqtr4g
end
