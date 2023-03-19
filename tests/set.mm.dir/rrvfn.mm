include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "rrvvf.mm"
include "ffn.mm"
include "syl.mm"

theorem rrvfn
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> X Fn U. dom P )

  proof
    wph
    cP
    cdm
    cuni
    #
    cr
    cX
    wf
    cX
    @0
    wfn
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvvf
    @0
    cr
    cX
    ffn
    syl
end
