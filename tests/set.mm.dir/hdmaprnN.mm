include "crn.mm"
include "cdvh.mm"
include "cfv.mm"
include "cbs.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "eqid.mm"
include "hdmapfnN.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "hdmapcl.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "clspn.mm"
include "cmpd.mm"
include "c0g.mm"
include "hdmaprnlem17N.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem hdmaprnN
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  assume hdmaprn.h: |- H = ( LHyp ` K )
  assume hdmaprn.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmaprn.d: |- D = ( Base ` C )
  assume hdmaprn.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaprn.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ran S = D )

  proof
    wph
    cS
    crn
    #
    cD
    wph
    cS
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    wfn
    vs
    cv
    #
    cS
    cfv
    cD
    wcel
    #
    vs
    @2
    wral
    @0
    cD
    wss
    wph
    cS
    @1
    cH
    cK
    @2
    cW
    hdmaprn.h
    @1
    eqid
    #
    @2
    eqid
    #
    hdmaprn.s
    hdmaprn.k
    hdmapfnN
    wph
    @4
    vs
    @2
    wph
    @3
    @2
    wcel
    #
    wa
    cC
    cD
    cS
    @3
    @1
    cH
    cK
    @2
    cW
    hdmaprn.h
    @5
    @6
    hdmaprn.c
    hdmaprn.d
    hdmaprn.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @7
    hdmaprn.k
    adantr
    wph
    @7
    simpr
    hdmapcl
    ralrimiva
    vs
    @2
    cD
    cS
    fnfvrnss
    syl2anc
    wph
    vs
    cD
    @0
    wph
    @3
    cD
    wcel
    #
    @3
    @0
    wcel
    wph
    @9
    wa
    cC
    cD
    cS
    @1
    cH
    cK
    cC
    clspn
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    @1
    clspn
    cfv
    #
    @2
    cW
    cC
    c0g
    cfv
    #
    vs
    hdmaprn.h
    @5
    @6
    @12
    eqid
    hdmaprn.c
    hdmaprn.d
    @13
    eqid
    @10
    eqid
    @11
    eqid
    hdmaprn.s
    wph
    @8
    @9
    hdmaprn.k
    adantr
    wph
    @9
    simpr
    hdmaprnlem17N
    ex
    ssrdv
    eqssd
end
