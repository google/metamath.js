include "cs7.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs8.mm"
include "s7eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s8.mm"
include "3eqtr4g.mm"

theorem s8eqd
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
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )
  assume s4eqd.4: |- ( ph -> D = Q )
  assume s5eqd.5: |- ( ph -> E = R )
  assume s6eqd.6: |- ( ph -> F = S )
  assume s7eqd.6: |- ( ph -> G = T )
  assume s8eqd.6: |- ( ph -> H = U )


  assert |- ( ph -> <" A B C D E F G H "> = <" N O P Q R S T U "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cs7
    #
    cH
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
    cT
    cs7
    #
    cU
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
    cH
    cs8
    cN
    cO
    cP
    cQ
    cR
    cS
    cT
    cU
    cs8
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
    cT
    cE
    cF
    cG
    cN
    cO
    s2eqd.1
    s2eqd.2
    s3eqd.3
    s4eqd.4
    s5eqd.5
    s6eqd.6
    s7eqd.6
    s7eqd
    wph
    cH
    cU
    s8eqd.6
    s1eqd
    oveq12d
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    df-s8
    cN
    cO
    cP
    cQ
    cR
    cS
    cT
    cU
    df-s8
    3eqtr4g
end
