include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "subcld.mm"
include "mulcomd.mm"
include "subdird.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem subdir2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )
  assume subdid.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( C x. ( A - B ) ) = ( ( C x. A ) - ( C x. B ) ) )

  proof
    wph
    cC
    cA
    cB
    cmin
    co
    #
    cmul
    co
    @0
    cC
    cmul
    co
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cmin
    co
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cmin
    co
    wph
    cC
    @0
    subdid.3
    wph
    cA
    cB
    mulm1d.1
    mulnegd.2
    subcld
    mulcomd
    wph
    cA
    cB
    cC
    mulm1d.1
    mulnegd.2
    subdid.3
    subdird
    wph
    @1
    @3
    @2
    @4
    cmin
    wph
    cA
    cC
    mulm1d.1
    subdid.3
    mulcomd
    wph
    cB
    cC
    mulnegd.2
    subdid.3
    mulcomd
    oveq12d
    3eqtrd
end
