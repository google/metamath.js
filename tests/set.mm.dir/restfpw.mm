include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "pwexg.mm"
include "adantr.mm"
include "inex1g.mm"
include "syl.mm"
include "ssexg.mm"
include "ancoms.mm"
include "restval.mm"
include "syl2anc.mm"
include "wf.mm"
include "inss2.mm"
include "a1i.mm"
include "elfpw.mm"
include "simprbi.mm"
include "adantl.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "simplbi.mm"
include "df-ss.mm"
include "sylib.mm"
include "simplr.mm"
include "sstrd.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem restfpw
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ B C_ A ) -> ( ( ~P A i^i Fin ) |`t B ) = ( ~P B i^i Fin ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cA
    cpw
    #
    cfn
    cin
    #
    cB
    crest
    co
    #
    cB
    cpw
    cfn
    cin
    #
    @2
    @5
    vx
    @4
    vx
    cv
    #
    cB
    cin
    #
    cmpt
    #
    crn
    #
    @6
    @2
    @4
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @5
    @10
    wceq
    @2
    @3
    cvv
    wcel
    #
    @11
    @0
    @13
    @1
    cA
    cV
    pwexg
    adantr
    @3
    cfn
    cvv
    inex1g
    syl
    #
    @1
    @0
    @12
    cB
    cA
    cV
    ssexg
    ancoms
    #
    vx
    cB
    @4
    cvv
    cvv
    restval
    syl2anc
    @2
    @4
    @6
    @9
    wf
    @10
    @6
    wss
    @2
    vx
    @4
    @8
    @6
    @9
    @2
    @7
    @4
    wcel
    #
    wa
    #
    @8
    cB
    wss
    #
    @8
    cfn
    wcel
    #
    @8
    @6
    wcel
    @18
    @17
    @7
    cB
    inss2
    a1i
    @17
    @7
    cfn
    wcel
    #
    @8
    @7
    wss
    @19
    @16
    @20
    @2
    @16
    @7
    cA
    wss
    #
    @20
    @7
    cA
    elfpw
    #
    simprbi
    adantl
    @7
    cB
    inss1
    @7
    @8
    ssfi
    sylancl
    @8
    cB
    elfpw
    sylanbrc
    @9
    eqid
    fmptd
    @4
    @6
    @9
    frn
    syl
    eqsstrd
    @2
    vx
    @6
    @5
    @2
    @7
    @6
    wcel
    #
    @7
    @5
    wcel
    @2
    @23
    wa
    #
    @8
    @7
    @5
    @24
    @7
    cB
    wss
    #
    @8
    @7
    wceq
    @23
    @25
    @2
    @23
    @25
    @20
    @7
    cB
    elfpw
    #
    simplbi
    adantl
    #
    @7
    cB
    df-ss
    sylib
    @24
    @11
    @12
    @16
    @8
    @5
    wcel
    @2
    @11
    @23
    @14
    adantr
    @2
    @12
    @23
    @15
    adantr
    @24
    @21
    @20
    @16
    @24
    @7
    cB
    cA
    @27
    @0
    @1
    @23
    simplr
    sstrd
    @23
    @20
    @2
    @23
    @25
    @20
    @26
    simprbi
    adantl
    @22
    sylanbrc
    @7
    cB
    @4
    cvv
    cvv
    elrestr
    syl3anc
    eqeltrrd
    ex
    ssrdv
    eqssd
end
