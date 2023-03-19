include "cpnf.mm"
include "crn.mm"
include "wcel.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simpr.mm"
include "sge0pnfval.mm"
include "cr.mm"
include "wn.mm"
include "sge0repnf.mm"
include "mpbid.mm"
include "pm2.65da.mm"

theorem sge0rern
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume sge0rern.x: |- ( ph -> X e. V )
  assume sge0rern.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0rern.re: |- ( ph -> ( sum^ ` F ) e. RR )


  assert |- ( ph -> -. +oo e. ran F )

  proof
    wph
    cpnf
    cF
    crn
    wcel
    #
    cF
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    wph
    @0
    wa
    #
    cF
    cV
    cX
    wph
    cX
    cV
    wcel
    @0
    sge0rern.x
    adantr
    #
    wph
    cX
    cc0
    cpnf
    cicc
    co
    cF
    wf
    @0
    sge0rern.f
    adantr
    #
    wph
    @0
    simpr
    sge0pnfval
    @3
    @1
    cr
    wcel
    #
    @2
    wn
    wph
    @6
    @0
    sge0rern.re
    adantr
    @3
    cF
    cV
    cX
    @4
    @5
    sge0repnf
    mpbid
    pm2.65da
end
