include "wcel.mm"
include "wf.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "wss.mm"
include "w3a.mm"
include "wpss.mm"
include "cfv.mm"
include "wceq.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "wbr.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "simp3.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "fpwwe.mm"
include "mpbiri.mm"
include "simpld.mm"
include "fpwwelem.mm"
include "mpbid.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "simprd.mm"
include "dmss.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "syl5ss.mm"
include "wor.mm"
include "wn.mm"
include "weso.mm"
include "sonr.mm"
include "syl2anc.mm"
include "eleq2i.mm"
include "wb.mm"
include "fvex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "bitri.mm"
include "sylnibr.mm"
include "ssnelpssd.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqcomd.mm"
include "3jca.mm"

theorem canth4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume canth4.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) }
  assume canth4.2: |- B = U. dom W
  assume canth4.3: |- C = ( `' ( W ` B ) " { ( F ` B ) } )

  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint D r
  disjoint D x
  disjoint D y
  disjoint F r
  disjoint F x
  disjoint F y
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint C y
  disjoint W r
  disjoint W x
  disjoint W y
  assert |- ( ( A e. V /\ F : D --> A /\ ( ~P A i^i dom card ) C_ D ) -> ( B C_ A /\ C C. B /\ ( F ` B ) = ( F ` C ) ) )

  proof
    cA
    cV
    wcel
    #
    cD
    cA
    cF
    wf
    #
    cA
    cpw
    ccrd
    cdm
    cin
    #
    cD
    wss
    #
    w3a
    #
    cB
    cA
    wss
    #
    cC
    cB
    wpss
    cB
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    wceq
    @4
    @5
    cB
    cW
    cfv
    #
    cB
    cB
    cxp
    #
    wss
    #
    @4
    @5
    @10
    wa
    #
    cB
    @8
    wwe
    #
    @8
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    cF
    cfv
    #
    @14
    wceq
    #
    vy
    cB
    wral
    #
    wa
    #
    @4
    cB
    @8
    cW
    wbr
    #
    @11
    @20
    wa
    @4
    @21
    @6
    cB
    wcel
    #
    @4
    @21
    @22
    wa
    cB
    cB
    wceq
    #
    @8
    @8
    wceq
    #
    wa
    @23
    @24
    cB
    eqid
    @8
    eqid
    pm3.2i
    @4
    vx
    vy
    cA
    @8
    cF
    cW
    cB
    cB
    vr
    canth4.1
    @0
    @1
    cA
    cvv
    wcel
    @3
    cA
    cV
    elex
    3ad2ant1
    #
    @4
    vx
    cv
    #
    @2
    wcel
    #
    wa
    cD
    cA
    @26
    cF
    @0
    @1
    @3
    @27
    simpl2
    @4
    @2
    cD
    @26
    @0
    @1
    @3
    simp3
    sselda
    ffvelrnd
    canth4.2
    fpwwe
    mpbiri
    #
    simpld
    @4
    vx
    vy
    cA
    @8
    cF
    cW
    cB
    vr
    canth4.1
    @25
    fpwwelem
    mpbid
    #
    simpld
    #
    simpld
    @4
    cC
    cB
    @6
    @4
    cC
    @8
    cdm
    #
    cB
    cC
    @13
    @6
    csn
    #
    cima
    #
    @31
    canth4.3
    @8
    @32
    cnvimass
    eqsstri
    @4
    @31
    @9
    cdm
    #
    cB
    @4
    @10
    @31
    @34
    wss
    @4
    @5
    @10
    @30
    simprd
    @8
    @9
    dmss
    syl
    cB
    dmxpid
    syl6sseq
    syl5ss
    @4
    @21
    @22
    @28
    simprd
    #
    @4
    @6
    @6
    @8
    wbr
    #
    @6
    cC
    wcel
    #
    @4
    cB
    @8
    wor
    #
    @22
    @36
    wn
    @4
    @12
    @38
    @4
    @12
    @19
    @4
    @11
    @20
    @29
    simprd
    #
    simpld
    cB
    @8
    weso
    syl
    @35
    cB
    @6
    @8
    sonr
    syl2anc
    @37
    @6
    @33
    wcel
    #
    @36
    cC
    @33
    @6
    canth4.3
    eleq2i
    @6
    cvv
    wcel
    @40
    @36
    wb
    cB
    cF
    fvex
    #
    @8
    @6
    @6
    cvv
    @41
    eliniseg
    ax-mp
    bitri
    sylnibr
    ssnelpssd
    @4
    @7
    @6
    @4
    @22
    @19
    @7
    @6
    wceq
    #
    @35
    @4
    @12
    @19
    @39
    simprd
    @18
    @42
    vy
    @6
    cB
    @14
    @6
    wceq
    #
    @17
    @7
    @14
    @6
    @43
    @16
    cC
    cF
    @43
    @16
    @33
    cC
    @43
    @15
    @32
    @13
    @14
    @6
    sneq
    imaeq2d
    canth4.3
    syl6eqr
    fveq2d
    @43
    id
    eqeq12d
    rspcv
    sylc
    eqcomd
    3jca
end
