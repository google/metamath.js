include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "eqid.mm"
include "idldil.mm"
include "cp0.mm"
include "simpll.mm"
include "simplrr.mm"
include "simprr.mm"
include "lhpmat.mm"
include "syl12anc.mm"
include "atbase.mm"
include "fvresi.mm"
include "3syl.mm"
include "oveq2d.mm"
include "simplll.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simplrl.mm"
include "simprl.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "isltrn.mm"
include "mpbir2and.mm"

theorem idltrn
  let cB: class B
  let cT: class T
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume idltrn.b: |- B = ( Base ` K )
  assume idltrn.h: |- H = ( LHyp ` K )
  assume idltrn.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( _I |` B ) e. T )

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
    cid
    cB
    cres
    #
    cT
    wcel
    @3
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    vp
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    vq
    cv
    #
    cW
    @6
    wbr
    wn
    #
    wa
    #
    @5
    @5
    @3
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    @8
    @8
    @3
    cfv
    #
    @12
    co
    #
    cW
    @14
    co
    #
    wceq
    #
    wi
    #
    vq
    cK
    catm
    cfv
    #
    wral
    vp
    @21
    wral
    chlt
    cB
    @4
    cH
    cK
    cW
    idltrn.b
    idltrn.h
    @4
    eqid
    #
    idldil
    @2
    @20
    vp
    vq
    @21
    @21
    @2
    @5
    @21
    wcel
    #
    @8
    @21
    wcel
    #
    wa
    #
    wa
    #
    @10
    @19
    @26
    @10
    wa
    #
    @8
    cW
    @14
    co
    #
    cK
    cp0
    cfv
    #
    @18
    @15
    @27
    @2
    @24
    @9
    @28
    @29
    wceq
    @2
    @25
    @10
    simpll
    #
    @2
    @23
    @24
    @10
    simplrr
    #
    @26
    @7
    @9
    simprr
    @21
    @8
    cH
    cK
    @6
    @14
    cW
    @29
    @6
    eqid
    #
    @14
    eqid
    #
    @29
    eqid
    #
    @21
    eqid
    #
    idltrn.h
    lhpmat
    syl12anc
    @27
    @17
    @8
    cW
    @14
    @27
    @17
    @8
    @8
    @12
    co
    #
    @8
    @27
    @16
    @8
    @8
    @12
    @27
    @24
    @8
    cB
    wcel
    @16
    @8
    wceq
    @31
    @21
    cB
    @8
    cK
    idltrn.b
    @35
    atbase
    cB
    @8
    fvresi
    3syl
    oveq2d
    @27
    @0
    @24
    @36
    @8
    wceq
    @0
    @1
    @25
    @10
    simplll
    #
    @31
    @21
    @12
    cK
    @8
    @12
    eqid
    #
    @35
    hlatjidm
    syl2anc
    eqtrd
    oveq1d
    @27
    @15
    @5
    cW
    @14
    co
    #
    @29
    @27
    @13
    @5
    cW
    @14
    @27
    @13
    @5
    @5
    @12
    co
    #
    @5
    @27
    @11
    @5
    @5
    @12
    @27
    @23
    @5
    cB
    wcel
    @11
    @5
    wceq
    @2
    @23
    @24
    @10
    simplrl
    #
    @21
    cB
    @5
    cK
    idltrn.b
    @35
    atbase
    cB
    @5
    fvresi
    3syl
    oveq2d
    @27
    @0
    @23
    @40
    @5
    wceq
    @37
    @41
    @21
    @12
    cK
    @5
    @38
    @35
    hlatjidm
    syl2anc
    eqtrd
    oveq1d
    @27
    @2
    @23
    @7
    @39
    @29
    wceq
    @30
    @41
    @26
    @7
    @9
    simprl
    @21
    @5
    cH
    cK
    @6
    @14
    cW
    @29
    @32
    @33
    @34
    @35
    idltrn.h
    lhpmat
    syl12anc
    eqtrd
    3eqtr4rd
    ex
    ralrimivva
    @21
    chlt
    @4
    cT
    @3
    cH
    @12
    cK
    @6
    @14
    cW
    vq
    vp
    @32
    @38
    @33
    @35
    idltrn.h
    @22
    idltrn.t
    isltrn
    mpbir2and
end
