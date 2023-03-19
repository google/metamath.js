include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "cxr.mm"
include "iccssxr.mm"
include "wor.mm"
include "wss.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "xrge0infss.mm"
include "syl.mm"
include "infcl.mm"
include "sseldi.mm"
include "sseldd.mm"
include "wcel.mm"
include "inflb.mm"
include "mpd.mm"
include "xrnltled.mm"

theorem infxrge0lb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume infxrge0lb.a: |- ( ph -> A C_ ( 0 [,] +oo ) )
  assume infxrge0lb.b: |- ( ph -> B e. A )


  assert |- ( ph -> inf ( A , ( 0 [,] +oo ) , < ) <_ B )

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
    #
    cB
    wph
    @0
    cxr
    @1
    cc0
    cpnf
    iccssxr
    #
    wph
    vx
    vy
    vz
    @0
    cA
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
    @3
    @2
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    a1i
    #
    wph
    cA
    @0
    wss
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    wn
    vy
    cA
    wral
    @6
    @5
    clt
    wbr
    vz
    cv
    @5
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
    infxrge0lb.a
    vx
    vy
    vz
    cA
    xrge0infss
    syl
    #
    infcl
    sseldi
    wph
    @0
    cxr
    cB
    @2
    wph
    cA
    @0
    cB
    infxrge0lb.a
    infxrge0lb.b
    sseldd
    sseldi
    wph
    cB
    cA
    wcel
    cB
    @1
    clt
    wbr
    wn
    infxrge0lb.b
    wph
    vx
    vy
    vz
    @0
    cA
    cB
    clt
    @4
    @7
    inflb
    mpd
    xrnltled
end
