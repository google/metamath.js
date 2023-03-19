include "clmod.mm"
include "wcel.mm"
include "clfig.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "clspn.mm"
include "crab.mm"
include "df-lfig.mm"
include "eleq2i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "ineq1d.mm"
include "imaeq12d.mm"
include "eleq12d.mm"
include "elrab3.mm"
include "syl5bb.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "clss.mm"
include "wf.mm"
include "eqid.mm"
include "lspf.mm"
include "ffn.mm"
include "syl.mm"
include "inss1.mm"
include "fvelimab.mm"
include "sylancl.mm"
include "elin.mm"
include "eqcomi.mm"
include "pweqi.mm"
include "anbi1i.mm"
include "bitri.mm"
include "eqeq2i.mm"
include "anbi12i.mm"
include "anass.mm"
include "rexbii2.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem islmodfg
  let cB: class B
  let cN: class N
  let cW: class W
  let vb: setvar b
  let va: setvar a
  assume islmodfg.b: |- B = ( Base ` W )
  assume islmodfg.n: |- N = ( LSpan ` W )

  disjoint W b
  disjoint B b
  disjoint N b
  disjoint W a
  disjoint a b
  disjoint B a
  disjoint N a
  assert |- ( W e. LMod -> ( W e. LFinGen <-> E. b e. ~P B ( b e. Fin /\ ( N ` b ) = B ) ) )

  proof
    cW
    clmod
    wcel
    #
    cW
    clfig
    wcel
    #
    cW
    cbs
    cfv
    #
    cN
    @2
    cpw
    #
    cfn
    cin
    #
    cima
    #
    wcel
    #
    vb
    cv
    #
    cfn
    wcel
    #
    @7
    cN
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vb
    cB
    cpw
    #
    wrex
    #
    @1
    cW
    va
    cv
    #
    cbs
    cfv
    #
    @14
    clspn
    cfv
    #
    @15
    cpw
    #
    cfn
    cin
    #
    cima
    #
    wcel
    #
    va
    clmod
    crab
    #
    wcel
    @0
    @6
    clfig
    @21
    cW
    va
    df-lfig
    eleq2i
    @20
    @6
    va
    cW
    clmod
    @14
    cW
    wceq
    #
    @15
    @2
    @19
    @5
    @14
    cW
    cbs
    fveq2
    #
    @22
    @16
    cN
    @18
    @4
    @22
    @16
    cW
    clspn
    cfv
    cN
    @14
    cW
    clspn
    fveq2
    islmodfg.n
    syl6eqr
    @22
    @17
    @3
    cfn
    @22
    @15
    @2
    @23
    pweqd
    ineq1d
    imaeq12d
    eleq12d
    elrab3
    syl5bb
    @0
    @6
    @9
    @2
    wceq
    #
    vb
    @4
    wrex
    #
    @13
    @0
    cN
    @3
    wfn
    #
    @4
    @3
    wss
    @6
    @25
    wb
    @0
    @3
    cW
    clss
    cfv
    #
    cN
    wf
    @26
    @27
    cN
    @2
    cW
    @2
    eqid
    @27
    eqid
    islmodfg.n
    lspf
    @3
    @27
    cN
    ffn
    syl
    @3
    cfn
    inss1
    vb
    @3
    @4
    @2
    cN
    fvelimab
    sylancl
    @24
    @11
    vb
    @4
    @12
    @7
    @4
    wcel
    #
    @24
    wa
    @7
    @12
    wcel
    #
    @8
    wa
    #
    @10
    wa
    @29
    @11
    wa
    @28
    @30
    @24
    @10
    @28
    @7
    @3
    wcel
    #
    @8
    wa
    @30
    @7
    @3
    cfn
    elin
    @31
    @29
    @8
    @3
    @12
    @7
    @2
    cB
    cB
    @2
    islmodfg.b
    eqcomi
    #
    pweqi
    eleq2i
    anbi1i
    bitri
    @2
    cB
    @9
    @32
    eqeq2i
    anbi12i
    @29
    @8
    @10
    anass
    bitri
    rexbii2
    syl6bb
    bitrd
end
