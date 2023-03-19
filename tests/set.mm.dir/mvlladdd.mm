include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "pncand.mm"
include "addcomd.mm"
include "eqtr3d.mm"
include "oveq1d.mm"

theorem mvlladdd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvlladdd.1: |- ( ph -> A e. CC )
  assume mvlladdd.2: |- ( ph -> B e. CC )
  assume mvlladdd.3: |- ( ph -> ( A + B ) = C )


  assert |- ( ph -> B = ( C - A ) )

  proof
    wph
    cB
    cA
    caddc
    co
    #
    cA
    cmin
    co
    cB
    cC
    cA
    cmin
    co
    wph
    cB
    cA
    mvlladdd.2
    mvlladdd.1
    pncand
    wph
    @0
    cC
    cA
    cmin
    wph
    cA
    cB
    caddc
    co
    @0
    cC
    wph
    cA
    cB
    mvlladdd.1
    mvlladdd.2
    addcomd
    mvlladdd.3
    eqtr3d
    oveq1d
    eqtr3d
end
