include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "wb.mm"
include "lsslmod.mm"
include "eqid.mm"
include "islss3.mm"
include "syl.mm"
include "wceq.mm"
include "lssss.mm"
include "adantl.mm"
include "ressbas2.mm"
include "sseq2d.mm"
include "anbi1d.mm"
include "sstr2.mm"
include "mpan9.mm"
include "biantrurd.mm"
include "oveq1i.mm"
include "ressabs.mm"
include "adantll.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "ad2antrr.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "syl6bb.mm"
include "3bitr2d.mm"

theorem lsslss
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  assume lsslss.x: |- X = ( W |`s U )
  assume lsslss.s: |- S = ( LSubSp ` W )
  assume lsslss.t: |- T = ( LSubSp ` X )


  assert |- ( ( W e. LMod /\ U e. S ) -> ( V e. T <-> ( V e. S /\ V C_ U ) ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cV
    cT
    wcel
    #
    cV
    cX
    cbs
    cfv
    #
    wss
    #
    cX
    cV
    cress
    co
    #
    clmod
    wcel
    #
    wa
    #
    cV
    cU
    wss
    #
    @7
    wa
    #
    cV
    cS
    wcel
    #
    @9
    wa
    #
    @2
    cX
    clmod
    wcel
    @3
    @8
    wb
    cS
    cU
    cW
    cX
    lsslss.x
    lsslss.s
    lsslmod
    cT
    cV
    @4
    cX
    @6
    @6
    eqid
    @4
    eqid
    lsslss.t
    islss3
    syl
    @2
    @9
    @5
    @7
    @2
    cU
    @4
    cV
    @2
    cU
    cW
    cbs
    cfv
    #
    wss
    #
    cU
    @4
    wceq
    @1
    @14
    @0
    cS
    cU
    @13
    cW
    @13
    eqid
    #
    lsslss.s
    lssss
    adantl
    #
    cU
    @13
    cX
    cW
    lsslss.x
    @15
    ressbas2
    syl
    sseq2d
    anbi1d
    @2
    @10
    @9
    @11
    wa
    @12
    @2
    @9
    @7
    @11
    @2
    @9
    wa
    #
    cW
    cV
    cress
    co
    #
    clmod
    wcel
    #
    cV
    @13
    wss
    #
    @19
    wa
    #
    @7
    @11
    @17
    @20
    @19
    @2
    @14
    @9
    @20
    @16
    cV
    cU
    @13
    sstr2
    mpan9
    biantrurd
    @17
    @6
    @18
    clmod
    @17
    @6
    cW
    cU
    cress
    co
    #
    cV
    cress
    co
    #
    @18
    cX
    @22
    cV
    cress
    lsslss.x
    oveq1i
    @1
    @9
    @23
    @18
    wceq
    @0
    cU
    cV
    cW
    cS
    ressabs
    adantll
    syl5eq
    eleq1d
    @0
    @11
    @21
    wb
    @1
    @9
    cS
    cV
    @13
    cW
    @18
    @18
    eqid
    @15
    lsslss.s
    islss3
    ad2antrr
    3bitr4d
    pm5.32da
    @9
    @11
    ancom
    syl6bb
    3bitr2d
end
