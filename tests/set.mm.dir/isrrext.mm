include "cnrg.mm"
include "cdr.mm"
include "cin.mm"
include "wcel.mm"
include "cnlm.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "ccusp.mm"
include "cuss.mm"
include "cmetu.mm"
include "crrext.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "czlm.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "eleq1i.mm"
include "syl6bbr.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "df-rrext.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem isrrext
  let cB: class B
  let cD: class D
  let cR: class R
  let cZ: class Z
  let vr: setvar r
  assume isrrext.b: |- B = ( Base ` R )
  assume isrrext.v: |- D = ( ( dist ` R ) |` ( B X. B ) )
  assume isrrext.z: |- Z = ( ZMod ` R )


  assert |- ( R e. RRExt <-> ( ( R e. NrmRing /\ R e. DivRing ) /\ ( Z e. NrmMod /\ ( chr ` R ) = 0 ) /\ ( R e. CUnifSp /\ ( UnifSt ` R ) = ( metUnif ` D ) ) ) )

  proof
    cR
    cnrg
    cdr
    cin
    #
    wcel
    #
    cZ
    cnlm
    wcel
    #
    cR
    cchr
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    cR
    ccusp
    wcel
    #
    cR
    cuss
    cfv
    #
    cD
    cmetu
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    cR
    cnrg
    wcel
    cR
    cdr
    wcel
    wa
    #
    @11
    wa
    cR
    crrext
    wcel
    @12
    @5
    @10
    w3a
    @1
    @12
    @11
    cR
    cnrg
    cdr
    elin
    anbi1i
    vr
    cv
    #
    czlm
    cfv
    #
    cnlm
    wcel
    #
    @13
    cchr
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @13
    ccusp
    wcel
    #
    @13
    cuss
    cfv
    #
    @13
    cds
    cfv
    #
    @13
    cbs
    cfv
    #
    @22
    cxp
    #
    cres
    #
    cmetu
    cfv
    #
    wceq
    #
    wa
    #
    wa
    @11
    vr
    cR
    @0
    crrext
    @13
    cR
    wceq
    #
    @18
    @5
    @27
    @10
    @28
    @15
    @2
    @17
    @4
    @28
    @15
    cR
    czlm
    cfv
    #
    cnlm
    wcel
    @2
    @28
    @14
    @29
    cnlm
    @13
    cR
    czlm
    fveq2
    eleq1d
    cZ
    @29
    cnlm
    isrrext.z
    eleq1i
    syl6bbr
    @28
    @16
    @3
    cc0
    @13
    cR
    cchr
    fveq2
    eqeq1d
    anbi12d
    @28
    @19
    @6
    @26
    @9
    @13
    cR
    ccusp
    eleq1
    @28
    @20
    @7
    @25
    @8
    @13
    cR
    cuss
    fveq2
    @28
    @24
    cD
    cmetu
    @28
    @24
    cR
    cds
    cfv
    #
    cB
    cB
    cxp
    #
    cres
    cD
    @28
    @21
    @30
    @23
    @31
    @13
    cR
    cds
    fveq2
    @28
    @22
    cB
    @28
    @22
    cR
    cbs
    cfv
    cB
    @13
    cR
    cbs
    fveq2
    isrrext.b
    syl6eqr
    sqxpeqd
    reseq12d
    isrrext.v
    syl6eqr
    fveq2d
    eqeq12d
    anbi12d
    anbi12d
    vr
    df-rrext
    elrab2
    @12
    @5
    @10
    3anass
    3bitr4i
end
