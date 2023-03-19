include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "lsatlss.mm"
include "syl.mm"
include "sseldd.mm"

theorem lsatlssel
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cU: class U
  let cW: class W
  let vv: setvar v
  assume lsatlss.s: |- S = ( LSubSp ` W )
  assume lsatlss.a: |- A = ( LSAtoms ` W )
  assume lssatssel.w: |- ( ph -> W e. LMod )
  assume lssatssel.u: |- ( ph -> U e. A )


  assert |- ( ph -> U e. S )

  proof
    wph
    cA
    cS
    cU
    wph
    cW
    clmod
    wcel
    cA
    cS
    wss
    lssatssel.w
    cA
    cS
    cW
    lsatlss.s
    lsatlss.a
    lsatlss
    syl
    lssatssel.u
    sseldd
end
