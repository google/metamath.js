include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wcel.mm"
include "wb.mm"
include "wor.mm"
include "cxr.mm"
include "wss.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "xrge0infss.mm"
include "syl.mm"
include "infglbb.mm"
include "mpdan.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "syl6bbr.mm"

theorem infxrge0glb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  assume infxrge0glb.a: |- ( ph -> A C_ ( 0 [,] +oo ) )
  assume infxrge0glb.b: |- ( ph -> B e. ( 0 [,] +oo ) )

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint ph z
  assert |- ( ph -> ( inf ( A , ( 0 [,] +oo ) , < ) < B <-> E. x e. A x < B ) )

  proof
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    cB
    clt
    wbr
    #
    vz
    cv
    #
    cB
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    vx
    cv
    #
    cB
    clt
    wbr
    #
    vx
    cA
    wrex
    wph
    cB
    @0
    wcel
    @1
    @4
    wb
    infxrge0glb.b
    wph
    vx
    vy
    vz
    @0
    cA
    cB
    clt
    @0
    clt
    wor
    #
    wph
    @0
    cxr
    wss
    cxr
    clt
    wor
    @7
    cc0
    cpnf
    iccssxr
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    a1i
    wph
    cA
    @0
    wss
    vy
    cv
    #
    @5
    clt
    wbr
    wn
    vy
    cA
    wral
    @5
    @8
    clt
    wbr
    @2
    @8
    clt
    wbr
    vz
    cA
    wrex
    wi
    vy
    @0
    wral
    wa
    vx
    @0
    wrex
    infxrge0glb.a
    vx
    vy
    vz
    cA
    xrge0infss
    syl
    infxrge0glb.a
    infglbb
    mpdan
    @6
    @3
    vx
    vz
    cA
    @5
    @2
    cB
    clt
    breq1
    cbvrexv
    syl6bbr
end
