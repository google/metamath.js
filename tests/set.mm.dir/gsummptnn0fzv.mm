include "nfv.mm"
include "gsummptnn0fz.mm"

theorem gsummptnn0fzv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cG: class G
  let c.0: class .0.
  assume gsummptnn0fzv.b: |- B = ( Base ` G )
  assume gsummptnn0fzv.0: |- .0. = ( 0g ` G )
  assume gsummptnn0fzv.g: |- ( ph -> G e. CMnd )
  assume gsummptnn0fzv.f: |- ( ph -> A. k e. NN0 C e. B )
  assume gsummptnn0fzv.s: |- ( ph -> S e. NN0 )
  assume gsummptnn0fzv.u: |- ( ph -> A. k e. NN0 ( S < k -> C = .0. ) )

  disjoint B k
  disjoint S k
  disjoint .0. k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. NN0 |-> C ) ) = ( G gsum ( k e. ( 0 ... S ) |-> C ) ) )

  proof
    wph
    cB
    cC
    cS
    vk
    cG
    c.0
    wph
    vk
    nfv
    gsummptnn0fzv.b
    gsummptnn0fzv.0
    gsummptnn0fzv.g
    gsummptnn0fzv.f
    gsummptnn0fzv.s
    gsummptnn0fzv.u
    gsummptnn0fz
end
