include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "simpll.mm"
include "csiga.mm"
include "crn.mm"
include "measbase.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "cr.mm"
include "eqidd.mm"
include "ineq1.mm"
include "0in.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "adantl.mm"
include "measvnul.mm"
include "eqtrd.mm"
include "adantr.mm"
include "0elsiga.mm"
include "syl.mm"
include "0red.mm"
include "fvmptd.mm"
include "measinblem.mm"
include "simplll.mm"
include "simprl.mm"
include "sigaclcu.mm"
include "simpllr.mm"
include "wss.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "esumeq2dv.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "wb.mm"
include "ismeas.mm"
include "mpbir3and.mm"

theorem measinb
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint S x
  disjoint M x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint S y
  disjoint S z
  disjoint M y
  disjoint M z
  assert |- ( ( M e. ( measures ` S ) /\ A e. S ) -> ( x e. S |-> ( M ` ( x i^i A ) ) ) e. ( measures ` S ) )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cA
    cS
    wcel
    #
    wa
    #
    vx
    cS
    vx
    cv
    #
    cA
    cin
    #
    cM
    cfv
    #
    cmpt
    #
    @0
    wcel
    #
    cS
    cc0
    cpnf
    cicc
    co
    #
    @7
    wf
    #
    c0
    @7
    cfv
    cc0
    wceq
    #
    vz
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @12
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @12
    cuni
    #
    @7
    cfv
    #
    @12
    @14
    @7
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vz
    cS
    cpw
    #
    wral
    #
    @3
    vx
    cS
    @6
    @9
    @7
    @3
    @4
    cS
    wcel
    #
    wa
    #
    @1
    @5
    cS
    wcel
    #
    @6
    @9
    wcel
    @1
    @2
    @25
    simpll
    @26
    cS
    csiga
    crn
    cuni
    wcel
    #
    @25
    @2
    @27
    @1
    @28
    @2
    @25
    cS
    cM
    measbase
    #
    ad2antrr
    @3
    @25
    simpr
    @1
    @2
    @25
    simplr
    @4
    cA
    cS
    inelsiga
    syl3anc
    @5
    cS
    cM
    measvxrge0
    syl2anc
    @7
    eqid
    fmptd
    @3
    vx
    c0
    @6
    cc0
    cS
    @7
    cr
    @3
    @7
    eqidd
    @3
    @4
    c0
    wceq
    #
    wa
    @6
    c0
    cM
    cfv
    #
    cc0
    @30
    @6
    @31
    wceq
    @3
    @30
    @5
    c0
    cM
    @30
    @5
    c0
    cA
    cin
    c0
    @4
    c0
    cA
    ineq1
    cA
    0in
    syl6eq
    fveq2d
    adantl
    @1
    @31
    cc0
    wceq
    @2
    @30
    cS
    cM
    measvnul
    ad2antrr
    eqtrd
    @3
    @28
    c0
    cS
    wcel
    @1
    @28
    @2
    @29
    adantr
    #
    cS
    0elsiga
    syl
    @3
    0red
    fvmptd
    @3
    @22
    vz
    @23
    @3
    @12
    @23
    wcel
    #
    wa
    #
    @16
    @21
    @34
    @16
    wa
    #
    @17
    cA
    cin
    #
    cM
    cfv
    #
    @12
    @14
    cA
    cin
    #
    cM
    cfv
    #
    vy
    cesum
    #
    @18
    @20
    vy
    cA
    @12
    cS
    cM
    measinblem
    @35
    vx
    @17
    @6
    @37
    cS
    @7
    @9
    @35
    @7
    eqidd
    @35
    @4
    @17
    wceq
    #
    wa
    @5
    @36
    cM
    @41
    @5
    @36
    wceq
    @35
    @4
    @17
    cA
    ineq1
    adantl
    fveq2d
    @35
    @28
    @33
    @13
    @17
    cS
    wcel
    #
    @35
    @1
    @28
    @1
    @2
    @33
    @16
    simplll
    #
    @29
    syl
    #
    @3
    @33
    @16
    simplr
    @34
    @13
    @15
    simprl
    @12
    cS
    sigaclcu
    syl3anc
    #
    @35
    @1
    @36
    cS
    wcel
    #
    @37
    @9
    wcel
    @43
    @35
    @28
    @42
    @2
    @46
    @44
    @45
    @1
    @2
    @33
    @16
    simpllr
    @17
    cA
    cS
    inelsiga
    syl3anc
    @36
    cS
    cM
    measvxrge0
    syl2anc
    fvmptd
    @34
    @20
    @40
    wceq
    @16
    @34
    @12
    @19
    @39
    vy
    @34
    @14
    @12
    wcel
    #
    wa
    #
    vx
    @14
    @6
    @39
    cS
    @7
    @9
    @48
    @7
    eqidd
    @48
    @4
    @14
    wceq
    #
    wa
    @5
    @38
    cM
    @49
    @5
    @38
    wceq
    @48
    @4
    @14
    cA
    ineq1
    adantl
    fveq2d
    @48
    @12
    cS
    @14
    @33
    @12
    cS
    wss
    @3
    @47
    @12
    cS
    elpwi
    ad2antlr
    @34
    @47
    simpr
    sseldd
    #
    @48
    @1
    @38
    cS
    wcel
    #
    @39
    @9
    wcel
    @1
    @2
    @33
    @47
    simplll
    #
    @48
    @28
    @14
    cS
    wcel
    @2
    @51
    @48
    @1
    @28
    @52
    @29
    syl
    @50
    @1
    @2
    @33
    @47
    simpllr
    @14
    cA
    cS
    inelsiga
    syl3anc
    @38
    cS
    cM
    measvxrge0
    syl2anc
    fvmptd
    esumeq2dv
    adantr
    3eqtr4d
    ex
    ralrimiva
    @3
    @28
    @8
    @10
    @11
    @24
    w3a
    wb
    @32
    vz
    vy
    cS
    @7
    ismeas
    syl
    mpbir3and
end
