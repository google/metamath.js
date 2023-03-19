include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "claut.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "simpll.mm"
include "eqid.mm"
include "ldillaut.mm"
include "lautcnv.mm"
include "syl2anc.mm"
include "w3a.mm"
include "ldilval.mm"
include "3expa.mm"
include "3impb.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "ldil1o.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "f1ocnvfv1.mm"
include "eqtr3d.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "wb.mm"
include "isldil.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem ldilcnv
  let cD: class D
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume ldilcnv.h: |- H = ( LHyp ` K )
  assume ldilcnv.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. D ) -> `' F e. D )

  proof
    cK
    chlt
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
    wa
    #
    cF
    ccnv
    #
    cD
    wcel
    #
    @5
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
    @9
    @5
    cfv
    #
    @9
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
    @4
    @0
    cF
    @7
    wcel
    @8
    @0
    @1
    @3
    simpll
    cD
    cF
    cH
    @7
    cK
    chlt
    cW
    ldilcnv.h
    @7
    eqid
    #
    ldilcnv.d
    ldillaut
    cF
    @7
    cK
    chlt
    @17
    lautcnv
    syl2anc
    @4
    @14
    vx
    @15
    @4
    @9
    @15
    wcel
    #
    @11
    @13
    @4
    @18
    @11
    w3a
    #
    @9
    cF
    cfv
    #
    @5
    cfv
    #
    @12
    @9
    @19
    @20
    @9
    @5
    @4
    @18
    @11
    @20
    @9
    wceq
    #
    @2
    @3
    @18
    @11
    wa
    @22
    @15
    cD
    cF
    cH
    cK
    @10
    chlt
    cW
    @9
    @15
    eqid
    #
    @10
    eqid
    #
    ldilcnv.h
    ldilcnv.d
    ldilval
    3expa
    3impb
    fveq2d
    @19
    @15
    @15
    cF
    wf1o
    #
    @18
    @21
    @9
    wceq
    @4
    @18
    @25
    @11
    @15
    cD
    cF
    cH
    cK
    chlt
    cW
    @23
    ldilcnv.h
    ldilcnv.d
    ldil1o
    3ad2ant1
    @4
    @18
    @11
    simp2
    @15
    @15
    @9
    cF
    f1ocnvfv1
    syl2anc
    eqtr3d
    3exp
    ralrimiv
    @2
    @6
    @8
    @16
    wa
    wb
    @3
    vx
    @15
    chlt
    cD
    @5
    cH
    @7
    cK
    @10
    cW
    @23
    @24
    ldilcnv.h
    @17
    ldilcnv.d
    isldil
    adantr
    mpbir2and
end
