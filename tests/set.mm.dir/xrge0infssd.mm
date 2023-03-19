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
include "sstrd.mm"
include "infssd.mm"
include "xrnltled.mm"

theorem xrge0infssd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrge0infssd.1: |- ( ph -> C C_ B )
  assume xrge0infssd.2: |- ( ph -> B C_ ( 0 [,] +oo ) )


  assert |- ( ph -> inf ( B , ( 0 [,] +oo ) , < ) <_ inf ( C , ( 0 [,] +oo ) , < ) )

  proof
    wph
    cB
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    #
    cC
    @0
    clt
    cinf
    #
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
    @4
    @3
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    a1i
    #
    wph
    cB
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
    #
    vy
    cB
    wral
    @7
    @6
    clt
    wbr
    #
    vz
    cv
    @6
    clt
    wbr
    #
    vz
    cB
    wrex
    wi
    vy
    @0
    wral
    wa
    vx
    @0
    wrex
    xrge0infssd.2
    vx
    vy
    vz
    cB
    xrge0infss
    syl
    #
    infcl
    sseldi
    wph
    @0
    cxr
    @2
    @3
    wph
    vx
    vy
    vz
    @0
    cC
    clt
    @5
    wph
    cC
    @0
    wss
    @8
    vy
    cC
    wral
    @9
    @10
    vz
    cC
    wrex
    wi
    vy
    @0
    wral
    wa
    vx
    @0
    wrex
    wph
    cC
    cB
    @0
    xrge0infssd.1
    xrge0infssd.2
    sstrd
    vx
    vy
    vz
    cC
    xrge0infss
    syl
    #
    infcl
    sseldi
    wph
    vx
    vy
    vz
    @0
    cB
    cC
    clt
    @5
    xrge0infssd.1
    @12
    @11
    infssd
    xrnltled
end
