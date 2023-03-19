include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "clt.mm"
include "csup.mm"
include "suprub.mm"
include "syl31anc.mm"

theorem suprubd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume suprubd.1: |- ( ph -> A C_ RR )
  assume suprubd.2: |- ( ph -> A =/= (/) )
  assume suprubd.3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume suprubd.4: |- ( ph -> B e. A )

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ph -> B <_ sup ( A , RR , < ) )

  proof
    wph
    cA
    cr
    wss
    cA
    c0
    wne
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    cB
    cA
    wcel
    cB
    cA
    cr
    clt
    csup
    cle
    wbr
    suprubd.1
    suprubd.2
    suprubd.3
    suprubd.4
    vx
    vy
    cA
    cB
    suprub
    syl31anc
end
