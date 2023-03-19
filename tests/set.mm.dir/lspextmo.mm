include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cres.mm"
include "weq.mm"
include "wi.mm"
include "clmhm.mm"
include "co.mm"
include "wral.mm"
include "wrmo.mm"
include "wcel.mm"
include "eqtr3.mm"
include "cin.mm"
include "cdm.mm"
include "inss1.mm"
include "dmss.mm"
include "ax-mp.mm"
include "wfn.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "ad2antrl.mm"
include "ffn.mm"
include "syl.mm"
include "adantrr.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "simplr.mm"
include "clmod.mm"
include "clss.mm"
include "lmhmlmod1.mm"
include "adantr.mm"
include "lmhmeql.mm"
include "simprr.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "expr.mm"
include "wb.mm"
include "3syl.mm"
include "simpll.mm"
include "fnreseql.mm"
include "fneqeql.mm"
include "syl2anc.mm"
include "3imtr4d.mm"
include "syl5.mm"
include "ralrimivva.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem lspextmo
  let cB: class B
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cK: class K
  let cX: class X
  let vh: setvar h
  assume lspextmo.b: |- B = ( Base ` S )
  assume lspextmo.k: |- K = ( LSpan ` S )

  disjoint B g
  disjoint F g
  disjoint K g
  disjoint S g
  disjoint T g
  disjoint X g
  disjoint B h
  disjoint g h
  disjoint F h
  disjoint K h
  disjoint S h
  disjoint T h
  disjoint X h
  assert |- ( ( X C_ B /\ ( K ` X ) = B ) -> E* g e. ( S LMHom T ) ( g |` X ) = F )

  proof
    cX
    cB
    wss
    #
    cX
    cK
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vg
    cv
    #
    cX
    cres
    #
    cF
    wceq
    #
    vh
    cv
    #
    cX
    cres
    #
    cF
    wceq
    #
    wa
    #
    vg
    vh
    weq
    #
    wi
    #
    vh
    cS
    cT
    clmhm
    co
    #
    wral
    vg
    @13
    wral
    @6
    vg
    @13
    wrmo
    @3
    @12
    vg
    vh
    @13
    @13
    @10
    @5
    @8
    wceq
    #
    @3
    @4
    @13
    wcel
    #
    @7
    @13
    wcel
    #
    wa
    #
    wa
    #
    @11
    @5
    @8
    cF
    eqtr3
    @18
    cX
    @4
    @7
    cin
    #
    cdm
    #
    wss
    #
    @20
    cB
    wceq
    #
    @14
    @11
    @3
    @17
    @21
    @22
    @3
    @17
    @21
    wa
    #
    wa
    #
    @20
    cB
    @24
    @4
    cdm
    #
    @20
    cB
    @19
    @4
    wss
    @20
    @25
    wss
    @4
    @7
    inss1
    @19
    @4
    dmss
    ax-mp
    @24
    @4
    cB
    wfn
    #
    @25
    cB
    wceq
    @3
    @17
    @26
    @21
    @18
    cB
    cT
    cbs
    cfv
    #
    @4
    wf
    #
    @26
    @15
    @28
    @3
    @16
    cB
    @27
    cS
    cT
    @4
    lspextmo.b
    @27
    eqid
    #
    lmhmf
    ad2antrl
    cB
    @27
    @4
    ffn
    syl
    #
    adantrr
    cB
    @4
    fndm
    syl
    syl5sseq
    @24
    cB
    @1
    @20
    @0
    @2
    @23
    simplr
    @24
    cS
    clmod
    wcel
    #
    @20
    cS
    clss
    cfv
    #
    wcel
    #
    @21
    @1
    @20
    wss
    @17
    @31
    @3
    @21
    @15
    @31
    @16
    cS
    cT
    @4
    lmhmlmod1
    adantr
    ad2antrl
    @17
    @33
    @3
    @21
    cS
    cT
    @32
    @4
    @7
    @32
    eqid
    #
    lmhmeql
    ad2antrl
    @3
    @17
    @21
    simprr
    @32
    cX
    @20
    cK
    cS
    @34
    lspextmo.k
    lspssp
    syl3anc
    eqsstr3d
    eqssd
    expr
    @18
    @26
    @7
    cB
    wfn
    #
    @0
    @14
    @21
    wb
    @30
    @18
    @16
    cB
    @27
    @7
    wf
    @35
    @3
    @15
    @16
    simprr
    cB
    @27
    cS
    cT
    @7
    lspextmo.b
    @29
    lmhmf
    cB
    @27
    @7
    ffn
    3syl
    #
    @0
    @2
    @17
    simpll
    cB
    @4
    @7
    cX
    fnreseql
    syl3anc
    @18
    @26
    @35
    @11
    @22
    wb
    @30
    @36
    cB
    @4
    @7
    fneqeql
    syl2anc
    3imtr4d
    syl5
    ralrimivva
    @6
    @9
    vg
    vh
    @13
    @11
    @5
    @8
    cF
    @4
    @7
    cX
    reseq1
    eqeq1d
    rmo4
    sylibr
end
