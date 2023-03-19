include "clmod.mm"
include "wcel.mm"
include "cnzr.mm"
include "wa.mm"
include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "cvv.mm"
include "wf1.mm"
include "crn.mm"
include "clinds.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "lindff1.mm"
include "3expa.mm"
include "ssv.mm"
include "f1ss.mm"
include "sylancl.mm"
include "lindfrn.mm"
include "adantlr.mm"
include "jca.mm"
include "simpll.mm"
include "simprr.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1of1.mm"
include "syl.mm"
include "ad2antrl.mm"
include "f1linds.mm"
include "syl3anc.mm"
include "impbida.mm"

theorem islindf3
  let cF: class F
  let cL: class L
  let cW: class W
  assume islindf3.l: |- L = ( Scalar ` W )


  assert |- ( ( W e. LMod /\ L e. NzRing ) -> ( F LIndF W <-> ( F : dom F -1-1-> _V /\ ran F e. ( LIndS ` W ) ) ) )

  proof
    cW
    clmod
    wcel
    #
    cL
    cnzr
    wcel
    #
    wa
    #
    cF
    cW
    clindf
    wbr
    #
    cF
    cdm
    #
    cvv
    cF
    wf1
    #
    cF
    crn
    #
    cW
    clinds
    cfv
    wcel
    #
    wa
    #
    @2
    @3
    wa
    #
    @5
    @7
    @9
    @4
    cW
    cbs
    cfv
    #
    cF
    wf1
    #
    @10
    cvv
    wss
    @5
    @0
    @1
    @3
    @11
    @10
    cF
    cL
    cW
    @10
    eqid
    islindf3.l
    lindff1
    3expa
    @10
    ssv
    @4
    @10
    cvv
    cF
    f1ss
    sylancl
    @0
    @3
    @7
    @1
    cF
    cW
    lindfrn
    adantlr
    jca
    @2
    @8
    wa
    @0
    @7
    @4
    @6
    cF
    wf1
    #
    @3
    @0
    @1
    @8
    simpll
    @2
    @5
    @7
    simprr
    @5
    @12
    @2
    @7
    @5
    @4
    @6
    cF
    wf1o
    @12
    @4
    cvv
    cF
    f1f1orn
    @4
    @6
    cF
    f1of1
    syl
    ad2antrl
    @4
    @6
    cF
    cW
    f1linds
    syl3anc
    impbida
end
