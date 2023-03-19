include "wf.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "fvco3.mm"
include "syl2anc.mm"

theorem fvco3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume fvco3d.1: |- ( ph -> G : A --> B )
  assume fvco3d.2: |- ( ph -> C e. A )


  assert |- ( ph -> ( ( F o. G ) ` C ) = ( F ` ( G ` C ) ) )

  proof
    wph
    cA
    cB
    cG
    wf
    cC
    cA
    wcel
    cC
    cF
    cG
    ccom
    cfv
    cC
    cG
    cfv
    cF
    cfv
    wceq
    fvco3d.1
    fvco3d.2
    cA
    cB
    cC
    cF
    cG
    fvco3
    syl2anc
end
