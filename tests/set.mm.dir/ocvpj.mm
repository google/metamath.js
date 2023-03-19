include "cphl.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "clss.mm"
include "clsm.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "wss.mm"
include "ccss.mm"
include "eqid.mm"
include "pjcss.mm"
include "sselda.mm"
include "cssss.mm"
include "syl.mm"
include "ocvlss.mm"
include "syldan.mm"
include "cabl.mm"
include "csubg.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmodabl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "csslss.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "cssi.mm"
include "oveq2d.mm"
include "pjdm2.mm"
include "simplbda.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "mpbir2and.mm"

theorem ocvpj
  let cT: class T
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume ocvpj.k: |- K = ( proj ` W )
  assume ocvpj.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( W e. PreHil /\ T e. dom K ) -> ( ._|_ ` T ) e. dom K )

  proof
    cW
    cphl
    wcel
    #
    cT
    cK
    cdm
    #
    wcel
    #
    wa
    #
    cT
    c.pe
    cfv
    #
    @1
    wcel
    #
    @4
    cW
    clss
    cfv
    #
    wcel
    #
    @4
    @4
    c.pe
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    cW
    cbs
    cfv
    #
    wceq
    #
    @0
    @2
    cT
    @11
    wss
    #
    @7
    @3
    cT
    cW
    ccss
    cfv
    #
    wcel
    #
    @13
    @0
    @1
    @14
    cT
    @14
    cK
    cW
    ocvpj.k
    @14
    eqid
    #
    pjcss
    sselda
    #
    @14
    cT
    @11
    cW
    @11
    eqid
    #
    @16
    cssss
    syl
    cT
    @6
    c.pe
    @11
    cW
    @18
    ocvpj.o
    @6
    eqid
    #
    ocvlss
    syldan
    #
    @3
    @4
    cT
    @9
    co
    #
    cT
    @4
    @9
    co
    #
    @10
    @11
    @3
    cW
    cabl
    wcel
    #
    @4
    cW
    csubg
    cfv
    #
    wcel
    cT
    @24
    wcel
    @21
    @22
    wceq
    @3
    cW
    clmod
    wcel
    #
    @23
    @0
    @25
    @2
    cW
    phllmod
    adantr
    #
    cW
    lmodabl
    syl
    @3
    @6
    @24
    @4
    @3
    @25
    @6
    @24
    wss
    @26
    @6
    cW
    @19
    lsssssubg
    syl
    #
    @20
    sseldd
    @3
    @6
    @24
    cT
    @27
    @0
    @2
    @15
    cT
    @6
    wcel
    #
    @17
    @14
    cT
    @6
    cW
    @16
    @19
    csslss
    syldan
    sseldd
    @9
    @4
    cT
    cW
    @9
    eqid
    #
    lsmcom
    syl3anc
    @3
    cT
    @8
    @4
    @9
    @3
    @15
    cT
    @8
    wceq
    @17
    @14
    cT
    c.pe
    cW
    ocvpj.o
    @16
    cssi
    syl
    oveq2d
    @0
    @2
    @28
    @22
    @11
    wceq
    @9
    cT
    cK
    @6
    c.pe
    @11
    cW
    @18
    @19
    ocvpj.o
    @29
    ocvpj.k
    pjdm2
    simplbda
    3eqtr3d
    @0
    @5
    @7
    @12
    wa
    wb
    @2
    @9
    @4
    cK
    @6
    c.pe
    @11
    cW
    @18
    @19
    ocvpj.o
    @29
    ocvpj.k
    pjdm2
    adantr
    mpbir2and
end
