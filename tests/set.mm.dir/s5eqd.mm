include "cs4.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs5.mm"
include "s4eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s5.mm"
include "3eqtr4g.mm"

theorem s5eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )
  assume s4eqd.4: |- ( ph -> D = Q )
  assume s5eqd.5: |- ( ph -> E = R )


  assert |- ( ph -> <" A B C D E "> = <" N O P Q R "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cs4
    #
    cE
    cs1
    #
    cconcat
    co
    cN
    cO
    cP
    cQ
    cs4
    #
    cR
    cs1
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cE
    cs5
    cN
    cO
    cP
    cQ
    cR
    cs5
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
    cN
    cO
    s2eqd.1
    s2eqd.2
    s3eqd.3
    s4eqd.4
    s4eqd
    wph
    cE
    cR
    s5eqd.5
    s1eqd
    oveq12d
    cA
    cB
    cC
    cD
    cE
    df-s5
    cN
    cO
    cP
    cQ
    cR
    df-s5
    3eqtr4g
end
