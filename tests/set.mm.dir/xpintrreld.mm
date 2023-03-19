include "cxp.mm"
include "ccom.mm"
include "wss.mm"
include "xptrrel.mm"
include "a1i.mm"
include "trrelind.mm"

theorem xpintrreld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume xpintrreld.r: |- ( ph -> ( R o. R ) C_ R )
  assume xpintrreld.s: |- ( ph -> S = ( R i^i ( A X. B ) ) )


  assert |- ( ph -> ( S o. S ) C_ S )

  proof
    wph
    cR
    cA
    cB
    cxp
    #
    cS
    xpintrreld.r
    @0
    @0
    ccom
    @0
    wss
    wph
    cA
    cB
    xptrrel
    a1i
    xpintrreld.s
    trrelind
end
