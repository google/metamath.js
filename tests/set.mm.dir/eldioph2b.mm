include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cfn.mm"
include "wn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cdioph.mm"
include "cfv.mm"
include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "cuz.mm"
include "eldiophb.mm"
include "wf1.mm"
include "cid.mm"
include "cz.mm"
include "ccom.mm"
include "cmpt.mm"
include "wf.mm"
include "simp-5r.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "f1f.mm"
include "syl.mm"
include "mzprename.mm"
include "syl3anc.mm"
include "w3a.mm"
include "diophrw.mm"
include "eqcomd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wex.mm"
include "simplll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "eldioph2lem2.mm"
include "syl22anc.mm"
include "rexv.mm"
include "sylibr.mm"
include "r19.29a.mm"
include "eqeq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "adantld.mm"
include "syl5bi.mm"
include "simpr.mm"
include "simpllr.mm"
include "eldioph2.mm"
include "syl121anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem eldioph2b
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cS: class S
  let cN: class N
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e

  disjoint A p
  disjoint N u
  disjoint N t
  disjoint N p
  disjoint t u
  disjoint p u
  disjoint p t
  disjoint S u
  disjoint S t
  disjoint S p
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a u
  disjoint a t
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b u
  disjoint b t
  disjoint c d
  disjoint c e
  disjoint c u
  disjoint c t
  disjoint c p
  disjoint d e
  disjoint d u
  disjoint d t
  disjoint d p
  disjoint e u
  disjoint e t
  disjoint e p
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  assert |- ( ( ( N e. NN0 /\ S e. _V ) /\ ( -. S e. Fin /\ ( 1 ... N ) C_ S ) ) -> ( A e. ( Dioph ` N ) <-> E. p e. ( mzPoly ` S ) A = { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1 ... N ) ) /\ ( p ` u ) = 0 ) } ) )

  proof
    cN
    cn0
    wcel
    #
    cS
    cvv
    wcel
    #
    wa
    #
    cS
    cfn
    wcel
    wn
    #
    c1
    cN
    cfz
    co
    #
    cS
    wss
    #
    wa
    #
    wa
    #
    cA
    cN
    cdioph
    cfv
    #
    wcel
    #
    cA
    vt
    cv
    #
    vu
    cv
    #
    @4
    cres
    wceq
    #
    @11
    vp
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    cS
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    wceq
    #
    vp
    cS
    cmzp
    cfv
    #
    wrex
    #
    @9
    @0
    cA
    @10
    vd
    cv
    #
    @4
    cres
    wceq
    @23
    vb
    cv
    #
    cfv
    cc0
    wceq
    wa
    vd
    cn0
    c1
    va
    cv
    #
    cfz
    co
    #
    cmap
    co
    wrex
    vt
    cab
    #
    wceq
    #
    vb
    @26
    cmzp
    cfv
    #
    wrex
    va
    cN
    cuz
    cfv
    #
    wrex
    #
    wa
    @7
    @22
    vd
    vt
    cA
    va
    cN
    vb
    eldiophb
    @7
    @31
    @22
    @0
    @7
    @28
    @22
    va
    vb
    @30
    @29
    @7
    @25
    @30
    wcel
    #
    @24
    @29
    wcel
    #
    wa
    #
    wa
    #
    @22
    @28
    @27
    @19
    wceq
    #
    vp
    @21
    wrex
    #
    @35
    @26
    cS
    vc
    cv
    #
    wf1
    #
    @38
    @4
    cres
    cid
    @4
    cres
    wceq
    #
    wa
    #
    @37
    vc
    cvv
    @35
    @38
    cvv
    wcel
    #
    wa
    #
    @41
    wa
    #
    ve
    cz
    cS
    cmap
    co
    ve
    cv
    @38
    ccom
    @24
    cfv
    cmpt
    #
    @21
    wcel
    #
    @27
    @12
    @11
    @45
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    @17
    wrex
    #
    vt
    cab
    #
    wceq
    #
    @37
    @44
    @1
    @33
    @26
    cS
    @38
    wf
    #
    @46
    @0
    @1
    @6
    @34
    @42
    @41
    simp-5r
    #
    @35
    @33
    @42
    @41
    @7
    @32
    @33
    simprr
    ad2antrr
    @44
    @39
    @53
    @43
    @39
    @40
    simprl
    #
    @26
    cS
    @38
    f1f
    syl
    ve
    @38
    @24
    @26
    cS
    mzprename
    syl3anc
    @44
    @1
    @39
    @40
    @52
    @54
    @55
    @43
    @39
    @40
    simprr
    @1
    @39
    @40
    w3a
    @51
    @27
    @24
    cS
    @26
    @38
    @4
    vt
    vu
    vd
    ve
    diophrw
    eqcomd
    syl3anc
    @36
    @52
    vp
    @45
    @21
    @13
    @45
    wceq
    #
    @19
    @51
    @27
    @56
    @18
    @50
    vt
    @56
    @16
    @49
    vu
    @17
    @56
    @15
    @48
    @12
    @56
    @14
    @47
    cc0
    @11
    @13
    @45
    fveq1
    eqeq1d
    anbi2d
    rexbidv
    abbidv
    eqeq2d
    rspcev
    syl2anc
    @35
    @41
    vc
    wex
    #
    @41
    vc
    cvv
    wrex
    @35
    @0
    @3
    @5
    @32
    @57
    @0
    @1
    @6
    @34
    simplll
    @2
    @3
    @5
    @34
    simplrl
    @2
    @3
    @5
    @34
    simplrr
    @7
    @32
    @33
    simprl
    @25
    cS
    cN
    vc
    eldioph2lem2
    syl22anc
    @41
    vc
    rexv
    sylibr
    r19.29a
    @28
    @20
    @36
    vp
    @21
    cA
    @27
    @19
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdvva
    adantld
    syl5bi
    @7
    @20
    @9
    vp
    @21
    @7
    @13
    @21
    wcel
    #
    wa
    #
    @20
    @9
    @59
    @20
    wa
    cA
    @19
    @8
    @59
    @20
    simpr
    @59
    @19
    @8
    wcel
    #
    @20
    @59
    @0
    @1
    @5
    @58
    @60
    @0
    @1
    @6
    @58
    simplll
    @0
    @1
    @6
    @58
    simpllr
    @2
    @3
    @5
    @58
    simplrr
    @7
    @58
    simpr
    vu
    vt
    @13
    cS
    cN
    eldioph2
    syl121anc
    adantr
    eqeltrd
    ex
    rexlimdva
    impbid
end
