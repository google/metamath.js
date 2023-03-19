include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "rrvdm.mm"
include "eqimss2.mm"
include "syl.mm"

theorem rrvdmss
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> U. dom P C_ dom X )

  proof
    wph
    cX
    cdm
    #
    cP
    cdm
    cuni
    #
    wceq
    @1
    @0
    wss
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvdm
    @1
    @0
    eqimss2
    syl
end
