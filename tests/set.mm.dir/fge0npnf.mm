include "cpnf.mm"
include "crn.mm"
include "wcel.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wa.mm"
include "wss.mm"
include "wf.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "wn.mm"
include "cxr.mm"
include "0xr.mm"
include "icoub.mm"
include "ax-mp.mm"
include "a1i.mm"
include "pm2.65da.mm"

theorem fge0npnf
  let wph: wff ph
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fge0npnf.1: |- ( ph -> F : X --> ( 0 [,) +oo ) )


  assert |- ( ph -> -. +oo e. ran F )

  proof
    wph
    cpnf
    cF
    crn
    #
    wcel
    #
    cpnf
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    wph
    @1
    wa
    #
    @0
    @2
    cpnf
    wph
    @0
    @2
    wss
    #
    @1
    wph
    cX
    @2
    cF
    wf
    @5
    fge0npnf.1
    cX
    @2
    cF
    frn
    syl
    adantr
    wph
    @1
    simpr
    sseldd
    @3
    wn
    #
    @4
    cc0
    cxr
    wcel
    @6
    0xr
    cc0
    cpnf
    icoub
    ax-mp
    a1i
    pm2.65da
end
