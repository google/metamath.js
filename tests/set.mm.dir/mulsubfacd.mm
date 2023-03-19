include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem mulsubfacd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume muls1d.1: |- ( ph -> A e. CC )
  assume muls1d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A x. B ) - B ) = ( ( A - 1 ) x. B ) )

  proof
    wph
    cA
    c1
    cmin
    co
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    #
    c1
    cB
    cmul
    co
    #
    cmin
    co
    @0
    cB
    cmin
    co
    wph
    cA
    c1
    cB
    muls1d.1
    wph
    1cnd
    muls1d.2
    subdird
    wph
    @1
    cB
    @0
    cmin
    wph
    cB
    muls1d.2
    mulid2d
    oveq2d
    eqtr2d
end
