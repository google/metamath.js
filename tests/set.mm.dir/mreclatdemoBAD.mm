include "ctps.mm"
include "clmod.mm"
include "cin.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccld.mm"
include "cuni.mm"
include "cmre.mm"
include "cipo.mm"
include "ccla.mm"
include "cpw.mm"
include "cvv.mm"
include "fvex.mm"
include "uniex.mm"
include "mremre.mm"
include "mp1i.mm"
include "cbs.mm"
include "inss2.mm"
include "sseli.mm"
include "eqid.mm"
include "lssmre.mm"
include "syl.mm"
include "wceq.mm"
include "inss1.mm"
include "tpsuni.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ctop.mm"
include "tpstop.mm"
include "cldmre.mm"
include "3syl.mm"
include "mreincl.mm"
include "syl3anc.mm"

theorem mreclatdemoBAD
  let cW: class W
  assume mreclatBAD.: |- ( ( ( LSubSp ` W ) i^i ( Clsd ` ( TopOpen ` W ) ) ) e. ( Moore ` U. ( TopOpen ` W ) ) -> ( toInc ` ( ( LSubSp ` W ) i^i ( Clsd ` ( TopOpen ` W ) ) ) ) e. CLat )


  assert |- ( W e. ( TopSp i^i LMod ) -> ( toInc ` ( ( LSubSp ` W ) i^i ( Clsd ` ( TopOpen ` W ) ) ) ) e. CLat )

  proof
    cW
    ctps
    clmod
    cin
    #
    wcel
    #
    cW
    clss
    cfv
    #
    cW
    ctopn
    cfv
    #
    ccld
    cfv
    #
    cin
    #
    @3
    cuni
    #
    cmre
    cfv
    #
    wcel
    #
    @5
    cipo
    cfv
    ccla
    wcel
    @1
    @7
    @6
    cpw
    #
    cmre
    cfv
    wcel
    #
    @2
    @7
    wcel
    @4
    @7
    wcel
    #
    @8
    @6
    cvv
    wcel
    @10
    @1
    @3
    cW
    ctopn
    fvex
    uniex
    cvv
    @6
    mremre
    mp1i
    @1
    @2
    cW
    cbs
    cfv
    #
    cmre
    cfv
    #
    @7
    @1
    cW
    clmod
    wcel
    @2
    @13
    wcel
    @0
    clmod
    cW
    ctps
    clmod
    inss2
    sseli
    @12
    @2
    cW
    @12
    eqid
    #
    @2
    eqid
    lssmre
    syl
    @1
    cW
    ctps
    wcel
    #
    @13
    @7
    wceq
    @0
    ctps
    cW
    ctps
    clmod
    inss1
    sseli
    #
    @15
    @12
    @6
    cmre
    @12
    @3
    cW
    @14
    @3
    eqid
    #
    tpsuni
    fveq2d
    syl
    eleqtrd
    @1
    @15
    @3
    ctop
    wcel
    @11
    @16
    @3
    cW
    @17
    tpstop
    @3
    @6
    @6
    eqid
    cldmre
    3syl
    @2
    @4
    @7
    @9
    mreincl
    syl3anc
    mreclatBAD.
    syl
end
