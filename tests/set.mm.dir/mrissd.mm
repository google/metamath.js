include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "mriss.mm"
include "syl2anc.mm"

theorem mrissd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume mriss.1: |- I = ( mrInd ` A )
  assume mrissd.2: |- ( ph -> A e. ( Moore ` X ) )
  assume mrissd.3: |- ( ph -> S e. I )


  assert |- ( ph -> S C_ X )

  proof
    wph
    cA
    cX
    cmre
    cfv
    wcel
    cS
    cI
    wcel
    cS
    cX
    wss
    mrissd.2
    mrissd.3
    cA
    cS
    cI
    cX
    mriss.1
    mriss
    syl2anc
end
