include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "bj-ldiv.mm"
include "bitrd.mm"

theorem bj-rdiv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume bj-ldiv.a: |- ( ph -> A e. CC )
  assume bj-ldiv.b: |- ( ph -> B e. CC )
  assume bj-ldiv.c: |- ( ph -> C e. CC )
  assume bj-rdiv.an0: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( ( A x. B ) = C <-> B = ( C / A ) ) )

  proof
    wph
    cA
    cB
    cmul
    co
    #
    cC
    wceq
    cB
    cA
    cmul
    co
    #
    cC
    wceq
    cB
    cC
    cA
    cdiv
    co
    wceq
    wph
    @0
    @1
    cC
    wph
    cA
    cB
    bj-ldiv.a
    bj-ldiv.b
    mulcomd
    eqeq1d
    wph
    cB
    cA
    cC
    bj-ldiv.b
    bj-ldiv.a
    bj-ldiv.c
    bj-rdiv.an0
    bj-ldiv
    bitrd
end
