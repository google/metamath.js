include "cs6.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs7.mm"
include "s6eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s7.mm"
include "3eqtr4g.mm"

theorem s7eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )
  assume s4eqd.4: |- ( ph -> D = Q )
  assume s5eqd.5: |- ( ph -> E = R )
  assume s6eqd.6: |- ( ph -> F = S )
  assume s7eqd.6: |- ( ph -> G = T )


  assert |- ( ph -> <" A B C D E F G "> = <" N O P Q R S T "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    #
    cG
    cs1
    #
    cconcat
    co
    cN
    cO
    cP
    cQ
    cR
    cS
    cs6
    #
    cT
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
    cG
    cs7
    cN
    cO
    cP
    cQ
    cR
    cS
    cT
    cs7
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
    cS
    cE
    cF
    cN
    cO
    s2eqd.1
    s2eqd.2
    s3eqd.3
    s4eqd.4
    s5eqd.5
    s6eqd.6
    s6eqd
    wph
    cG
    cT
    s7eqd.6
    s1eqd
    oveq12d
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    df-s7
    cN
    cO
    cP
    cQ
    cR
    cS
    cT
    df-s7
    3eqtr4g
end
