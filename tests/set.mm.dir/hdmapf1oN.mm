include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "hdmapfnN.mm"
include "hdmaprnN.mm"
include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "hdmap11.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem hdmapf1oN
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hdmapf1o.h: |- H = ( LHyp ` K )
  assume hdmapf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapf1o.v: |- V = ( Base ` U )
  assume hdmapf1o.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapf1o.d: |- D = ( Base ` C )
  assume hdmapf1o.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapf1o.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> S : V -1-1-onto-> D )

  proof
    wph
    cS
    cV
    wfn
    cS
    crn
    cD
    wceq
    vx
    cv
    #
    cS
    cfv
    vy
    cv
    #
    cS
    cfv
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cV
    wral
    vx
    cV
    wral
    cV
    cD
    cS
    wf1o
    wph
    cS
    cU
    cH
    cK
    cV
    cW
    hdmapf1o.h
    hdmapf1o.u
    hdmapf1o.v
    hdmapf1o.s
    hdmapf1o.k
    hdmapfnN
    wph
    cC
    cD
    cS
    cH
    cK
    cW
    hdmapf1o.h
    hdmapf1o.c
    hdmapf1o.d
    hdmapf1o.s
    hdmapf1o.k
    hdmaprnN
    wph
    @4
    vx
    vy
    cV
    cV
    wph
    @0
    cV
    wcel
    #
    @1
    cV
    wcel
    #
    wa
    #
    wa
    #
    @2
    @3
    @8
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    @1
    hdmapf1o.h
    hdmapf1o.u
    hdmapf1o.v
    hdmapf1o.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @7
    hdmapf1o.k
    adantr
    wph
    @5
    @6
    simprl
    wph
    @5
    @6
    simprr
    hdmap11
    biimpd
    ralrimivva
    vx
    vy
    cV
    cD
    cS
    dff1o6
    syl3anbrc
end
