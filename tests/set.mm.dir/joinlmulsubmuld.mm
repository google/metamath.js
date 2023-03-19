include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "subdird.mm"
include "eqtrd.mm"

theorem joinlmulsubmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x
  assume joinlmulsubmuld.1: |- ( ph -> A e. CC )
  assume joinlmulsubmuld.2: |- ( ph -> B e. CC )
  assume joinlmulsubmuld.3: |- ( ph -> C e. CC )
  assume joinlmulsubmuld.4: |- ( ph -> ( ( A x. B ) - ( C x. B ) ) = D )


  assert |- ( ph -> ( ( A - C ) x. B ) = D )

  proof
    wph
    cA
    cC
    cmin
    co
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    cC
    cB
    cmul
    co
    cmin
    co
    cD
    wph
    cA
    cC
    cB
    joinlmulsubmuld.1
    joinlmulsubmuld.3
    joinlmulsubmuld.2
    subdird
    joinlmulsubmuld.4
    eqtrd
end
