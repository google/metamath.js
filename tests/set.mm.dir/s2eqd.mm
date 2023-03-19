include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs2.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "df-s2.mm"
include "3eqtr4g.mm"

theorem s2eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let cO: class O
  assume s2eqd.1: |- ( ph -> A = N )
  assume s2eqd.2: |- ( ph -> B = O )


  assert |- ( ph -> <" A B "> = <" N O "> )

  proof
    wph
    cA
    cs1
    #
    cB
    cs1
    #
    cconcat
    co
    cN
    cs1
    #
    cO
    cs1
    #
    cconcat
    co
    cA
    cB
    cs2
    cN
    cO
    cs2
    wph
    @0
    @2
    @1
    @3
    cconcat
    wph
    cA
    cN
    s2eqd.1
    s1eqd
    wph
    cB
    cO
    s2eqd.2
    s1eqd
    oveq12d
    cA
    cB
    df-s2
    cN
    cO
    df-s2
    3eqtr4g
end
