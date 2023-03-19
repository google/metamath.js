include "cs3.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs4.mm"
include "s3eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s4.mm"
include "3eqtr4g.mm"

theorem s4eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )
  assume s4eqd.4: |- ( ph -> D = Q )


  assert |- ( ph -> <" A B C D "> = <" N O P Q "> )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cD
    cs1
    #
    cconcat
    co
    cN
    cO
    cP
    cs3
    #
    cQ
    cs1
    #
    cconcat
    co
    cA
    cB
    cC
    cD
    cs4
    cN
    cO
    cP
    cQ
    cs4
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
    cP
    cN
    cO
    s2eqd.1
    s2eqd.2
    s3eqd.3
    s3eqd
    wph
    cD
    cQ
    s4eqd.4
    s1eqd
    oveq12d
    cA
    cB
    cC
    cD
    df-s4
    cN
    cO
    cP
    cQ
    df-s4
    3eqtr4g
end
