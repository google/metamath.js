include "cvv.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "fvexd.mm"
include "salgencld.mm"
include "dmovnsal.mm"
include "borelmbl.mm"
include "smfsssmf.mm"

theorem bormflebmf
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume bormflebmf.x: |- ( ph -> X e. Fin )
  assume bormflebmf.b: |- B = ( SalGen ` ( TopOpen ` ( RR^ ` X ) ) )
  assume bormflebmf.l: |- L = dom ( voln ` X )
  assume bormflebmf.f: |- ( ph -> F e. ( SMblFn ` B ) )


  assert |- ( ph -> F e. ( SMblFn ` L ) )

  proof
    wph
    cB
    cL
    cF
    wph
    cB
    cvv
    cX
    crrx
    cfv
    #
    ctopn
    cfv
    wph
    @0
    ctopn
    fvexd
    bormflebmf.b
    salgencld
    wph
    cL
    cX
    bormflebmf.x
    bormflebmf.l
    dmovnsal
    wph
    cB
    cL
    cX
    bormflebmf.x
    bormflebmf.l
    bormflebmf.b
    borelmbl
    bormflebmf.f
    smfsssmf
end
