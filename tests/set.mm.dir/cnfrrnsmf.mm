include "cfn.mm"
include "wcel.mm"
include "ctop.mm"
include "rrxtop.mm"
include "syl.mm"
include "cnfsmf.mm"

theorem cnfrrnsmf
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume cnfrrnsmf.x: |- ( ph -> X e. Fin )
  assume cnfrrnsmf.j: |- J = ( TopOpen ` ( RR^ ` X ) )
  assume cnfrrnsmf.k: |- K = ( topGen ` ran (,) )
  assume cnfrrnsmf.f: |- ( ph -> F e. ( ( J |`t dom F ) Cn K ) )
  assume cnfrrnsmf.b: |- B = ( SalGen ` J )


  assert |- ( ph -> F e. ( SMblFn ` B ) )

  proof
    wph
    cB
    cF
    cJ
    cK
    wph
    cX
    cfn
    wcel
    cJ
    ctop
    wcel
    cnfrrnsmf.x
    cX
    cJ
    cfn
    cnfrrnsmf.j
    rrxtop
    syl
    cnfrrnsmf.k
    cnfrrnsmf.f
    cnfrrnsmf.b
    cnfsmf
end
