include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "claut.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "simp1l.mm"
include "eqid.mm"
include "ldillaut.mm"
include "3adant3.mm"
include "3adant2.mm"
include "lautco.mm"
include "syl3anc.mm"
include "wf.mm"
include "wf1o.mm"
include "simp11.mm"
include "simp13.mm"
include "ldil1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "simp2.mm"
include "fvco3.mm"
include "simp3.mm"
include "ldilval.mm"
include "syl112anc.mm"
include "fveq2d.mm"
include "simp12.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "wb.mm"
include "isldil.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem ldilco
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume ldilco.h: |- H = ( LHyp ` K )
  assume ldilco.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. D /\ G e. D ) -> ( F o. G ) e. D )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cD
    wcel
    #
    cG
    cD
    wcel
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cD
    wcel
    #
    @6
    cK
    claut
    cfv
    #
    wcel
    #
    vx
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @10
    @6
    cfv
    #
    @10
    wceq
    #
    wi
    #
    vx
    cK
    cbs
    cfv
    #
    wral
    #
    @5
    @0
    cF
    @8
    wcel
    #
    cG
    @8
    wcel
    #
    @9
    @0
    @1
    @3
    @4
    simp1l
    @2
    @3
    @18
    @4
    cD
    cF
    cH
    @8
    cK
    cV
    cW
    ldilco.h
    @8
    eqid
    #
    ldilco.d
    ldillaut
    3adant3
    @2
    @4
    @19
    @3
    cD
    cG
    cH
    @8
    cK
    cV
    cW
    ldilco.h
    @20
    ldilco.d
    ldillaut
    3adant2
    cF
    cG
    @8
    cK
    cV
    @20
    lautco
    syl3anc
    @5
    @15
    vx
    @16
    @5
    @10
    @16
    wcel
    #
    @12
    @14
    @5
    @21
    @12
    w3a
    #
    @13
    @10
    cG
    cfv
    #
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    @10
    @22
    @16
    @16
    cG
    wf
    #
    @21
    @13
    @24
    wceq
    @22
    @16
    @16
    cG
    wf1o
    #
    @26
    @22
    @2
    @4
    @27
    @2
    @3
    @4
    @21
    @12
    simp11
    #
    @2
    @3
    @4
    @21
    @12
    simp13
    #
    @16
    cD
    cG
    cH
    cK
    cV
    cW
    @16
    eqid
    #
    ldilco.h
    ldilco.d
    ldil1o
    syl2anc
    @16
    @16
    cG
    f1of
    syl
    @5
    @21
    @12
    simp2
    #
    @16
    @16
    @10
    cF
    cG
    fvco3
    syl2anc
    @22
    @23
    @10
    cF
    @22
    @2
    @4
    @21
    @12
    @23
    @10
    wceq
    @28
    @29
    @31
    @5
    @21
    @12
    simp3
    #
    @16
    cD
    cG
    cH
    cK
    @11
    cV
    cW
    @10
    @30
    @11
    eqid
    #
    ldilco.h
    ldilco.d
    ldilval
    syl112anc
    fveq2d
    @22
    @2
    @3
    @21
    @12
    @25
    @10
    wceq
    @28
    @2
    @3
    @4
    @21
    @12
    simp12
    @31
    @32
    @16
    cD
    cF
    cH
    cK
    @11
    cV
    cW
    @10
    @30
    @33
    ldilco.h
    ldilco.d
    ldilval
    syl112anc
    3eqtrd
    3exp
    ralrimiv
    @2
    @3
    @7
    @9
    @17
    wa
    wb
    @4
    vx
    @16
    cV
    cD
    @6
    cH
    @8
    cK
    @11
    cW
    @30
    @33
    ldilco.h
    @20
    ldilco.d
    isldil
    3ad2ant1
    mpbir2and
end
