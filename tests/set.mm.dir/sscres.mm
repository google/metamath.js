include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cssc.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "inss1.mm"
include "wceq.mm"
include "inss2.mm"
include "simpl.mm"
include "sseldi.mm"
include "simpr.mm"
include "ovresd.mm"
include "eqimss.mm"
include "syl.mm"
include "rgen2a.mm"
include "pm3.2i.mm"
include "fnssres.mm"
include "sylancl.mm"
include "resres.mm"
include "fnresdm.mm"
include "adantr.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "inxp.mm"
include "a1i.mm"
include "fneq12d.mm"
include "mpbid.mm"
include "isssc.mm"
include "mpbiri.mm"

theorem sscres
  let cS: class S
  let cT: class T
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( H Fn ( S X. S ) /\ S e. V ) -> ( H |` ( T X. T ) ) C_cat H )

  proof
    cH
    cS
    cS
    cxp
    #
    wfn
    #
    cS
    cV
    wcel
    #
    wa
    #
    cH
    cT
    cT
    cxp
    #
    cres
    #
    cH
    cssc
    wbr
    cS
    cT
    cin
    #
    cS
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    @5
    co
    #
    @8
    @9
    cH
    co
    #
    wss
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    wa
    @7
    @13
    cS
    cT
    inss1
    @12
    vx
    vy
    @6
    @8
    @6
    wcel
    #
    @9
    @6
    wcel
    #
    wa
    #
    @10
    @11
    wceq
    @12
    @16
    @8
    @9
    cH
    cT
    @16
    @6
    cT
    @8
    cS
    cT
    inss2
    #
    @14
    @15
    simpl
    sseldi
    @16
    @6
    cT
    @9
    @17
    @14
    @15
    simpr
    sseldi
    ovresd
    @10
    @11
    eqimss
    syl
    rgen2a
    pm3.2i
    @3
    vx
    vy
    @6
    cS
    @5
    cH
    cV
    @3
    cH
    @0
    @4
    cin
    #
    cres
    #
    @18
    wfn
    #
    @5
    @6
    @6
    cxp
    #
    wfn
    @3
    @1
    @18
    @0
    wss
    @20
    @1
    @2
    simpl
    #
    @0
    @4
    inss1
    @0
    @18
    cH
    fnssres
    sylancl
    @3
    @18
    @21
    @19
    @5
    @3
    @19
    cH
    @0
    cres
    #
    @4
    cres
    @5
    cH
    @0
    @4
    resres
    @3
    @23
    cH
    @4
    @1
    @23
    cH
    wceq
    @2
    @0
    cH
    fnresdm
    adantr
    reseq1d
    syl5eqr
    @18
    @21
    wceq
    @3
    cS
    cS
    cT
    cT
    inxp
    a1i
    fneq12d
    mpbid
    @22
    @1
    @2
    simpr
    isssc
    mpbiri
end
