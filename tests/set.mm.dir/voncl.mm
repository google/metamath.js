include "cvoln.mm"
include "cfv.mm"
include "vonmea.mm"
include "meacl.mm"

theorem voncl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume voncl.x: |- ( ph -> X e. Fin )
  assume voncl.s: |- S = dom ( voln ` X )
  assume voncl.a: |- ( ph -> A e. S )


  assert |- ( ph -> ( ( voln ` X ) ` A ) e. ( 0 [,] +oo ) )

  proof
    wph
    cA
    cS
    cX
    cvoln
    cfv
    wph
    cX
    voncl.x
    vonmea
    voncl.s
    voncl.a
    meacl
end
