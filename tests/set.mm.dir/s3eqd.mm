include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs3.mm"
include "s2eqd.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s3.mm"
include "3eqtr4g.mm"

theorem s3eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )
  assume s3eqd.3: |- ( ph -> C = P )


  assert |- ( ph -> <" A B C "> = <" N O P "> )

  proof
    wph
    cA
    cB
    cs2
    #
    cC
    cs1
    #
    cconcat
    co
    cN
    cO
    cs2
    #
    cP
    cs1
    #
    cconcat
    co
    cA
    cB
    cC
    cs3
    cN
    cO
    cP
    cs3
    wph
    @0
    @2
    @1
    @3
    cconcat
    wph
    cA
    cB
    cN
    cO
    s2eqd.1
    s2eqd.2
    s2eqd
    wph
    cC
    cP
    s3eqd.3
    s1eqd
    oveq12d
    cA
    cB
    cC
    df-s3
    cN
    cO
    cP
    df-s3
    3eqtr4g
end
