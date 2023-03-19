include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcomd.mm"
include "eqeq12d.mm"
include "mulcand.mm"
include "bitrd.mm"

theorem mulcan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume mulcand.1: |- ( ph -> A e. CC )
  assume mulcand.2: |- ( ph -> B e. CC )
  assume mulcand.3: |- ( ph -> C e. CC )
  assume mulcand.4: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A x. C ) = ( B x. C ) <-> A = B ) )

  proof
    wph
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
    wceq
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
    wceq
    cA
    cB
    wceq
    wph
    @0
    @2
    @1
    @3
    wph
    cA
    cC
    mulcand.1
    mulcand.3
    mulcomd
    wph
    cB
    cC
    mulcand.2
    mulcand.3
    mulcomd
    eqeq12d
    wph
    cA
    cB
    cC
    mulcand.1
    mulcand.2
    mulcand.3
    mulcand.4
    mulcand
    bitrd
end
