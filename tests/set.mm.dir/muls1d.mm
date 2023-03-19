include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "1cnd.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem muls1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume muls1d.1: |- ( ph -> A e. CC )
  assume muls1d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A x. ( B - 1 ) ) = ( ( A x. B ) - A ) )

  proof
    wph
    cA
    cB
    c1
    cmin
    co
    cmul
    co
    cA
    cB
    cmul
    co
    #
    cA
    c1
    cmul
    co
    #
    cmin
    co
    @0
    cA
    cmin
    co
    wph
    cA
    cB
    c1
    muls1d.1
    muls1d.2
    wph
    1cnd
    subdid
    wph
    @1
    cA
    @0
    cmin
    wph
    cA
    muls1d.1
    mulid1d
    oveq2d
    eqtrd
end
