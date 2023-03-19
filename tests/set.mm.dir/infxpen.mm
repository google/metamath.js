include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "csdm.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "copab.mm"
include "cin.mm"
include "coi.mm"
include "eqid.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "fveq2.mm"
include "uneq12d.mm"
include "adantr.mm"
include "adantl.mm"
include "eleq12d.mm"
include "eqeqan12d.mm"
include "breq12.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "cbvopabv.mm"
include "biid.mm"
include "infxpenlem.mm"

theorem infxpen
  let cA: class A
  let va: setvar a
  let vm: setvar m
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. On /\ _om C_ A ) -> ( A X. A ) ~~ A )

  proof
    va
    cv
    #
    con0
    wcel
    com
    vm
    cv
    #
    wss
    @1
    @1
    cxp
    @1
    cen
    wbr
    wi
    vm
    @0
    wral
    wa
    com
    @0
    wss
    @1
    @0
    csdm
    wbr
    vm
    @0
    wral
    wa
    wa
    #
    vx
    vy
    vz
    vw
    cA
    vs
    cv
    #
    con0
    con0
    cxp
    #
    wcel
    #
    vt
    cv
    #
    @4
    wcel
    #
    wa
    #
    @3
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cun
    #
    @6
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cun
    #
    wcel
    #
    @11
    @14
    wceq
    #
    @3
    @6
    vx
    cv
    #
    @4
    wcel
    vy
    cv
    #
    @4
    wcel
    wa
    @17
    c1st
    cfv
    #
    @18
    c1st
    cfv
    #
    wcel
    @19
    @20
    wceq
    @17
    c2nd
    cfv
    @18
    c2nd
    cfv
    wcel
    wa
    wo
    wa
    vx
    vy
    copab
    #
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    vs
    vt
    copab
    #
    @0
    @0
    cxp
    #
    @27
    cxp
    cin
    #
    @26
    vm
    @27
    @28
    coi
    #
    @21
    vw
    cv
    #
    c1st
    cfv
    #
    @30
    c2nd
    cfv
    #
    cun
    #
    va
    @21
    eqid
    @25
    vz
    cv
    #
    @4
    wcel
    #
    @30
    @4
    wcel
    #
    wa
    #
    @34
    c1st
    cfv
    #
    @34
    c2nd
    cfv
    #
    cun
    #
    @33
    wcel
    #
    @40
    @33
    wceq
    #
    @34
    @30
    @21
    wbr
    #
    wa
    #
    wo
    #
    wa
    vs
    vt
    vz
    vw
    @3
    @34
    wceq
    #
    @6
    @30
    wceq
    #
    wa
    #
    @8
    @37
    @24
    @45
    @46
    @5
    @35
    @47
    @7
    @36
    @3
    @34
    @4
    eleq1
    @6
    @30
    @4
    eleq1
    bi2anan9
    @48
    @15
    @41
    @23
    @44
    @48
    @11
    @40
    @14
    @33
    @46
    @11
    @40
    wceq
    @47
    @46
    @9
    @38
    @10
    @39
    @3
    @34
    c1st
    fveq2
    @3
    @34
    c2nd
    fveq2
    uneq12d
    #
    adantr
    @47
    @14
    @33
    wceq
    @46
    @47
    @12
    @31
    @13
    @32
    @6
    @30
    c1st
    fveq2
    @6
    @30
    c2nd
    fveq2
    uneq12d
    #
    adantl
    eleq12d
    @48
    @16
    @42
    @22
    @43
    @46
    @47
    @11
    @40
    @14
    @33
    @49
    @50
    eqeqan12d
    @3
    @34
    @6
    @30
    @21
    breq12
    anbi12d
    orbi12d
    anbi12d
    cbvopabv
    @28
    eqid
    @2
    biid
    @33
    eqid
    @29
    eqid
    infxpenlem
end
