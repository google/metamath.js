include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cpmap.mm"
include "wceq.mm"
include "wa.mm"
include "catm.mm"
include "wrex.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "eqid.mm"
include "isline2.mm"
include "syl.mm"
include "wi.mm"
include "cbs.mm"
include "adantr.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapsubclN.mm"
include "syldan.mm"
include "eleq1a.mm"
include "adantld.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "imp.mm"

theorem linepsubclN
  let cC: class C
  let cK: class K
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  assume linepsubcl.n: |- N = ( Lines ` K )
  assume linepsubcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. N ) -> X e. C )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cX
    cC
    wcel
    #
    @0
    @1
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cX
    @3
    @4
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vq
    cK
    catm
    cfv
    #
    wrex
    vp
    @12
    wrex
    #
    @2
    @0
    cK
    clat
    wcel
    #
    @1
    @13
    wb
    cK
    hllat
    #
    @12
    @6
    cK
    @8
    cN
    cX
    vq
    vp
    @6
    eqid
    #
    @12
    eqid
    #
    linepsubcl.n
    @8
    eqid
    #
    isline2
    syl
    @0
    @11
    @2
    vp
    vq
    @12
    @12
    @0
    @3
    @12
    wcel
    #
    @4
    @12
    wcel
    #
    wa
    #
    wa
    #
    @10
    @2
    @5
    @22
    @9
    cC
    wcel
    #
    @10
    @2
    wi
    @0
    @21
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @23
    @22
    @14
    @3
    @24
    wcel
    #
    @4
    @24
    wcel
    #
    @25
    @0
    @14
    @21
    @15
    adantr
    @19
    @26
    @0
    @20
    @12
    @24
    @3
    cK
    @24
    eqid
    #
    @17
    atbase
    ad2antrl
    @20
    @27
    @0
    @19
    @12
    @24
    @4
    cK
    @28
    @17
    atbase
    ad2antll
    @24
    @6
    cK
    @3
    @4
    @28
    @16
    latjcl
    syl3anc
    @24
    cC
    cK
    @8
    @7
    @28
    @18
    linepsubcl.c
    pmapsubclN
    syldan
    @9
    cC
    cX
    eleq1a
    syl
    adantld
    rexlimdvva
    sylbid
    imp
end
