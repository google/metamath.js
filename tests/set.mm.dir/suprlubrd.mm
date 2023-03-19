include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wcel.mm"
include "wb.mm"
include "suprlub.mm"
include "syl31anc.mm"
include "bicomd.mm"
include "biimpd.mm"
include "imp.mm"
include "mpdan.mm"

theorem suprlubrd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume suprlubrd.1: |- ( ph -> A C_ RR )
  assume suprlubrd.2: |- ( ph -> A =/= (/) )
  assume suprlubrd.3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume suprlubrd.4: |- ( ph -> B e. RR )
  assume suprlubrd.5: |- ( ph -> E. z e. A B < z )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint B z
  assert |- ( ph -> B < sup ( A , RR , < ) )

  proof
    wph
    cB
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    #
    cB
    cA
    cr
    clt
    csup
    clt
    wbr
    #
    suprlubrd.5
    wph
    @0
    @1
    wph
    @0
    @1
    wph
    @1
    @0
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
    cr
    wcel
    @1
    @0
    wb
    suprlubrd.1
    suprlubrd.2
    suprlubrd.3
    suprlubrd.4
    vx
    vy
    vz
    cA
    cB
    suprlub
    syl31anc
    bicomd
    biimpd
    imp
    mpdan
end
