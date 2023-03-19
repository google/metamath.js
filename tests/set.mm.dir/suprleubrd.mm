include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wcel.mm"
include "wb.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "bicomd.mm"
include "biimpd.mm"
include "imp.mm"
include "mpdan.mm"

theorem suprleubrd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume suprleubrd.1: |- ( ph -> A C_ RR )
  assume suprleubrd.2: |- ( ph -> A =/= (/) )
  assume suprleubrd.3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume suprleubrd.4: |- ( ph -> B e. RR )
  assume suprleubrd.5: |- ( ph -> A. z e. A z <_ B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint B z
  assert |- ( ph -> sup ( A , RR , < ) <_ B )

  proof
    wph
    vz
    cv
    cB
    cle
    wbr
    vz
    cA
    wral
    #
    cA
    cr
    clt
    csup
    cB
    cle
    wbr
    #
    suprleubrd.5
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
    suprleubrd.1
    suprleubrd.2
    suprleubrd.3
    suprleubrd.4
    vx
    vy
    vz
    cA
    cB
    suprleub
    syl31anc
    bicomd
    biimpd
    imp
    mpdan
end
