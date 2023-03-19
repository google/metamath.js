include "cuni.mm"
include "cin.mm"
include "cfv.mm"
include "cv.mm"
include "cesum.mm"
include "wss.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "elssuni.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "fveq2d.mm"
include "cmpt.mm"
include "cmeas.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cprb.mm"
include "domprobmeas.mm"
include "measinb.mm"
include "syl2anc.mm"
include "measvun.mm"
include "syl112anc.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "eqidd.mm"
include "wa.mm"
include "simpr.mm"
include "ineq1d.mm"
include "csiga.mm"
include "crn.mm"
include "domprobsiga.mm"
include "sigaclcu.mm"
include "syl3anc.mm"
include "inelsiga.mm"
include "prob01.mm"
include "fvmptd.mm"
include "adantr.mm"
include "elelpwi.mm"
include "esumeq2dv.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"

theorem totprobd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vb: setvar b
  let vc: setvar c
  assume totprobd.1: |- ( ph -> P e. Prob )
  assume totprobd.2: |- ( ph -> A e. dom P )
  assume totprobd.3: |- ( ph -> B e. ~P dom P )
  assume totprobd.4: |- ( ph -> U. B = U. dom P )
  assume totprobd.5: |- ( ph -> B ~<_ _om )
  assume totprobd.6: |- ( ph -> Disj_ b e. B b )

  disjoint A b
  disjoint B b
  disjoint P b
  disjoint b ph
  disjoint b c
  disjoint A c
  disjoint B c
  disjoint P c
  disjoint c ph
  assert |- ( ph -> ( P ` A ) = sum* b e. B ( P ` ( b i^i A ) ) )

  proof
    wph
    cB
    cuni
    #
    cA
    cin
    #
    cP
    cfv
    #
    cA
    cP
    cfv
    cB
    vb
    cv
    #
    cA
    cin
    #
    cP
    cfv
    #
    vb
    cesum
    #
    wph
    @1
    cA
    cP
    wph
    cA
    @0
    wss
    @1
    cA
    wceq
    wph
    cA
    cP
    cdm
    #
    cuni
    #
    @0
    wph
    cA
    @7
    wcel
    #
    cA
    @8
    wss
    totprobd.2
    cA
    @7
    elssuni
    syl
    totprobd.4
    sseqtr4d
    cA
    @0
    sseqin2
    sylib
    fveq2d
    wph
    @0
    vc
    @7
    vc
    cv
    #
    cA
    cin
    #
    cP
    cfv
    #
    cmpt
    #
    cfv
    #
    cB
    @3
    @13
    cfv
    #
    vb
    cesum
    #
    @2
    @6
    wph
    @13
    @7
    cmeas
    cfv
    #
    wcel
    #
    cB
    @7
    cpw
    wcel
    #
    cB
    com
    cdom
    wbr
    #
    vb
    cB
    @3
    wdisj
    @14
    @16
    wceq
    wph
    cP
    @17
    wcel
    #
    @9
    @18
    wph
    cP
    cprb
    wcel
    #
    @21
    totprobd.1
    cP
    domprobmeas
    syl
    totprobd.2
    vc
    cA
    @7
    cP
    measinb
    syl2anc
    totprobd.3
    totprobd.5
    totprobd.6
    vb
    cB
    @7
    @13
    measvun
    syl112anc
    wph
    vc
    @0
    @12
    @2
    @7
    @13
    cc0
    c1
    cicc
    co
    #
    wph
    @13
    eqidd
    wph
    @10
    @0
    wceq
    #
    wa
    #
    @11
    @1
    cP
    @25
    @10
    @0
    cA
    wph
    @24
    simpr
    ineq1d
    fveq2d
    wph
    @7
    csiga
    crn
    cuni
    wcel
    #
    @19
    @20
    @0
    @7
    wcel
    #
    wph
    @22
    @26
    totprobd.1
    cP
    domprobsiga
    syl
    #
    totprobd.3
    totprobd.5
    cB
    @7
    sigaclcu
    syl3anc
    #
    wph
    @22
    @1
    @7
    wcel
    #
    @2
    @23
    wcel
    totprobd.1
    wph
    @26
    @27
    @9
    @30
    @28
    @29
    totprobd.2
    @0
    cA
    @7
    inelsiga
    syl3anc
    @1
    cP
    prob01
    syl2anc
    fvmptd
    wph
    cB
    @15
    @5
    vb
    wph
    @3
    cB
    wcel
    #
    wa
    #
    vc
    @3
    @12
    @5
    @7
    @13
    @23
    @32
    @13
    eqidd
    @32
    @10
    @3
    wceq
    #
    wa
    #
    @11
    @4
    cP
    @34
    @10
    @3
    cA
    @32
    @33
    simpr
    ineq1d
    fveq2d
    @32
    @31
    @19
    @3
    @7
    wcel
    #
    wph
    @31
    simpr
    wph
    @19
    @31
    totprobd.3
    adantr
    @3
    cB
    @7
    elelpwi
    syl2anc
    #
    @32
    @22
    @4
    @7
    wcel
    #
    @5
    @23
    wcel
    wph
    @22
    @31
    totprobd.1
    adantr
    @32
    @26
    @35
    @9
    @37
    wph
    @26
    @31
    @28
    adantr
    @36
    wph
    @9
    @31
    totprobd.2
    adantr
    @3
    cA
    @7
    inelsiga
    syl3anc
    @4
    cP
    prob01
    syl2anc
    fvmptd
    esumeq2dv
    3eqtr3d
    eqtr3d
end
