include "cin.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "inss1.mm"
include "clvec.mm"
include "adantr.mm"
include "simpr.mm"
include "lshpcmp.mm"
include "mpbii.mm"
include "inss2.mm"
include "eqtr3d.mm"
include "ex.mm"
include "inidm.mm"
include "syl5eqel.mm"
include "ineq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem lshpinN
  let wph: wff ph
  let cT: class T
  let cU: class U
  let cH: class H
  let cW: class W
  assume lshpin.h: |- H = ( LSHyp ` W )
  assume lshpin.w: |- ( ph -> W e. LVec )
  assume lshpin.t: |- ( ph -> T e. H )
  assume lshpin.u: |- ( ph -> U e. H )


  assert |- ( ph -> ( ( T i^i U ) e. H <-> T = U ) )

  proof
    wph
    cT
    cU
    cin
    #
    cH
    wcel
    #
    cT
    cU
    wceq
    #
    wph
    @1
    @2
    wph
    @1
    wa
    #
    @0
    cT
    cU
    @3
    @0
    cT
    wss
    @0
    cT
    wceq
    cT
    cU
    inss1
    @3
    @0
    cT
    cH
    cW
    lshpin.h
    wph
    cW
    clvec
    wcel
    @1
    lshpin.w
    adantr
    #
    wph
    @1
    simpr
    #
    wph
    cT
    cH
    wcel
    @1
    lshpin.t
    adantr
    lshpcmp
    mpbii
    @3
    @0
    cU
    wss
    @0
    cU
    wceq
    cT
    cU
    inss2
    @3
    @0
    cU
    cH
    cW
    lshpin.h
    @4
    @5
    wph
    cU
    cH
    wcel
    @1
    lshpin.u
    adantr
    lshpcmp
    mpbii
    eqtr3d
    ex
    wph
    cT
    cT
    cin
    #
    cH
    wcel
    @2
    @1
    wph
    @6
    cT
    cH
    cT
    inidm
    lshpin.t
    syl5eqel
    @2
    @6
    @0
    cH
    cT
    cU
    cT
    ineq2
    eleq1d
    syl5ibcom
    impbid
end
