include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "suprcl.mm"
include "syl3anc.mm"

theorem suprcld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume suprcld.2: |- ( ph -> A C_ RR )
  assume suprcld.1: |- ( ph -> A =/= (/) )
  assume suprcld.4: |- ( ph -> E. x e. RR A. y e. A y <_ x )

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ph -> sup ( A , RR , < ) e. RR )

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
    cA
    cr
    clt
    csup
    cr
    wcel
    suprcld.2
    suprcld.1
    suprcld.4
    vx
    vy
    cA
    suprcl
    syl3anc
end
