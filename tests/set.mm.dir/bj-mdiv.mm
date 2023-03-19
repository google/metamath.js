include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "bj-ldiv.mm"
include "bj-rdiv.mm"
include "bitr3d.mm"

theorem bj-mdiv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume bj-ldiv.a: |- ( ph -> A e. CC )
  assume bj-ldiv.b: |- ( ph -> B e. CC )
  assume bj-ldiv.c: |- ( ph -> C e. CC )
  assume bj-mdiv.an0: |- ( ph -> A =/= 0 )
  assume bj-mdiv.bn0: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A = ( C / B ) <-> B = ( C / A ) ) )

  proof
    wph
    cA
    cB
    cmul
    co
    cC
    wceq
    cA
    cC
    cB
    cdiv
    co
    wceq
    cB
    cC
    cA
    cdiv
    co
    wceq
    wph
    cA
    cB
    cC
    bj-ldiv.a
    bj-ldiv.b
    bj-ldiv.c
    bj-mdiv.bn0
    bj-ldiv
    wph
    cA
    cB
    cC
    bj-ldiv.a
    bj-ldiv.b
    bj-ldiv.c
    bj-mdiv.an0
    bj-rdiv
    bitr3d
end
