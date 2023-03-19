include "ccmp.mm"
include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wa.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "ccl.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "c0.mm"
include "ciin.mm"
include "ctop.mm"
include "wceq.mm"
include "cmptop.mm"
include "cif.mm"
include "fclsval.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "sylan.mm"
include "fvex.mm"
include "dfiin3.mm"
include "ccld.mm"
include "wss.mm"
include "cfi.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "wf.mm"
include "adantr.mm"
include "syl.mm"
include "filelss.mm"
include "adantll.mm"
include "clscld.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "frn.mm"
include "simpr.mm"
include "clsss3.mm"
include "sscls.mm"
include "filss.mm"
include "syl13anc.mm"
include "fiss.mm"
include "filfi.mm"
include "sseqtrd.mm"
include "0nelfil.mm"
include "ssneldd.mm"
include "cmpfii.mm"
include "syl3anc.mm"
include "eqnetrd.mm"

theorem fclscmpi
  let cF: class F
  let cJ: class J
  let cX: class X
  let vg: setvar g
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume flimfnfcls.x: |- X = U. J


  assert |- ( ( J e. Comp /\ F e. ( Fil ` X ) ) -> ( J fClus F ) =/= (/) )

  proof
    cJ
    ccmp
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    wa
    #
    cJ
    cF
    cfcls
    co
    #
    vx
    cF
    vx
    cv
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cint
    #
    c0
    @3
    @4
    vx
    cF
    @7
    ciin
    #
    @10
    @0
    cJ
    ctop
    wcel
    #
    @2
    @4
    @11
    wceq
    cJ
    cmptop
    #
    @12
    @2
    wa
    @4
    cX
    cX
    wceq
    #
    @11
    c0
    cif
    @11
    vx
    cF
    cJ
    cX
    cX
    flimfnfcls.x
    fclsval
    @14
    @11
    c0
    cX
    eqid
    iftruei
    syl6eq
    sylan
    vx
    cF
    @7
    @5
    @6
    fvex
    dfiin3
    syl6eq
    @3
    @0
    @9
    cJ
    ccld
    cfv
    #
    wss
    #
    c0
    @9
    cfi
    cfv
    #
    wcel
    wn
    @10
    c0
    wne
    @0
    @2
    simpl
    #
    @3
    cF
    @15
    @8
    wf
    @16
    @3
    vx
    cF
    @7
    @15
    @8
    @3
    @5
    cF
    wcel
    #
    wa
    #
    @12
    @5
    cX
    wss
    #
    @7
    @15
    wcel
    @20
    @0
    @12
    @3
    @0
    @19
    @18
    adantr
    @13
    syl
    #
    @2
    @19
    @21
    @0
    @5
    cF
    cX
    filelss
    adantll
    #
    @5
    cJ
    cX
    flimfnfcls.x
    clscld
    syl2anc
    @8
    eqid
    #
    fmptd
    cF
    @15
    @8
    frn
    syl
    @3
    @17
    cF
    c0
    @3
    @17
    cF
    cfi
    cfv
    #
    cF
    @3
    @2
    @9
    cF
    wss
    #
    @17
    @25
    wss
    @0
    @2
    simpr
    #
    @3
    cF
    cF
    @8
    wf
    @26
    @3
    vx
    cF
    @7
    cF
    @8
    @20
    @2
    @19
    @7
    cX
    wss
    #
    @5
    @7
    wss
    #
    @7
    cF
    wcel
    @3
    @2
    @19
    @27
    adantr
    @3
    @19
    simpr
    @20
    @12
    @21
    @28
    @22
    @23
    @5
    cJ
    cX
    flimfnfcls.x
    clsss3
    syl2anc
    @20
    @12
    @21
    @29
    @22
    @23
    @5
    cJ
    cX
    flimfnfcls.x
    sscls
    syl2anc
    @5
    @7
    cF
    cX
    filss
    syl13anc
    @24
    fmptd
    cF
    cF
    @8
    frn
    syl
    @9
    cF
    @1
    fiss
    syl2anc
    @3
    @2
    @25
    cF
    wceq
    @27
    cF
    cX
    filfi
    syl
    sseqtrd
    @3
    @2
    c0
    cF
    wcel
    wn
    @27
    cF
    cX
    0nelfil
    syl
    ssneldd
    cJ
    @9
    cmpfii
    syl3anc
    eqnetrd
end
