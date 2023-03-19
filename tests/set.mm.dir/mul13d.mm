include "cmul.mm"
include "co.mm"
include "mul12d.mm"
include "mulassd.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "3eqtr2d.mm"

theorem mul13d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul13d.1: |- ( ph -> A e. CC )
  assume mul13d.2: |- ( ph -> B e. CC )
  assume mul13d.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A x. ( B x. C ) ) = ( C x. ( B x. A ) ) )

  proof
    wph
    cA
    cB
    cC
    cmul
    co
    cmul
    co
    cB
    cA
    cC
    cmul
    co
    cmul
    co
    cB
    cA
    cmul
    co
    #
    cC
    cmul
    co
    cC
    @0
    cmul
    co
    wph
    cA
    cB
    cC
    mul13d.1
    mul13d.2
    mul13d.3
    mul12d
    wph
    cB
    cA
    cC
    mul13d.2
    mul13d.1
    mul13d.3
    mulassd
    wph
    @0
    cC
    wph
    cB
    cA
    mul13d.2
    mul13d.1
    mulcld
    mul13d.3
    mulcomd
    3eqtr2d
end
