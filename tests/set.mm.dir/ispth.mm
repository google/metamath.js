include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "copab.mm"
include "pthsfval.mm"
include "3anass.mm"
include "opabbii.mm"
include "eqtri.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "adantr.mm"
include "reseq12d.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "preq2d.mm"
include "imaeq12d.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "reltrls.mm"
include "brfvopabrbr.mm"
include "bitr4i.mm"

theorem ispth
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- ( F ( Paths ` G ) P <-> ( F ( Trails ` G ) P /\ Fun `' ( P |` ( 1 ..^ ( # ` F ) ) ) /\ ( ( P " { 0 , ( # ` F ) } ) i^i ( P " ( 1 ..^ ( # ` F ) ) ) ) = (/) ) )

  proof
    cF
    cP
    cG
    cpths
    cfv
    #
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    #
    wbr
    #
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    #
    ccnv
    #
    wfun
    #
    cP
    cc0
    @3
    cpr
    #
    cima
    #
    cP
    @4
    cima
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    wa
    @2
    @7
    @12
    w3a
    vp
    cv
    #
    c1
    vf
    cv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    #
    ccnv
    #
    wfun
    #
    @14
    cc0
    @16
    cpr
    #
    cima
    #
    @14
    @17
    cima
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    @13
    vf
    vp
    cpths
    ctrls
    cF
    cP
    cG
    @0
    @15
    @14
    @1
    wbr
    #
    @20
    @25
    w3a
    #
    vf
    vp
    copab
    @27
    @26
    wa
    #
    vf
    vp
    copab
    vf
    cG
    vp
    pthsfval
    @28
    @29
    vf
    vp
    @27
    @20
    @25
    3anass
    opabbii
    eqtri
    @15
    cF
    wceq
    #
    @14
    cP
    wceq
    #
    wa
    #
    @20
    @7
    @25
    @12
    @32
    @19
    @6
    @32
    @18
    @5
    @32
    @14
    cP
    @17
    @4
    @30
    @31
    simpr
    #
    @30
    @17
    @4
    wceq
    @31
    @30
    @16
    @3
    c1
    cfzo
    @15
    cF
    chash
    fveq2
    #
    oveq2d
    adantr
    #
    reseq12d
    cnveqd
    funeqd
    @32
    @24
    @11
    c0
    @32
    @22
    @9
    @23
    @10
    @32
    @14
    cP
    @21
    @8
    @33
    @30
    @21
    @8
    wceq
    @31
    @30
    @16
    @3
    cc0
    @34
    preq2d
    adantr
    imaeq12d
    @32
    @14
    cP
    @17
    @4
    @33
    @35
    imaeq12d
    ineq12d
    eqeq1d
    anbi12d
    cG
    reltrls
    brfvopabrbr
    @2
    @7
    @12
    3anass
    bitr4i
end
