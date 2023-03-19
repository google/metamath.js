include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cpj1.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cphl.mm"
include "wceq.mm"
include "eqid.mm"
include "pjdm.mm"
include "wb.mm"
include "cplusg.mm"
include "c0g.mm"
include "ccntz.mm"
include "csubg.mm"
include "clmod.mm"
include "wss.mm"
include "phllmod.mm"
include "adantr.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "lssss.mm"
include "ocvlss.mm"
include "sylan2.mm"
include "ocvin.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "pj1f.mm"
include "adantl.mm"
include "fssd.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "feq2.mm"
include "biimpcd.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem pjdm2
  let c.po: class .(+)
  let cT: class T
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume pjdm2.v: |- V = ( Base ` W )
  assume pjdm2.l: |- L = ( LSubSp ` W )
  assume pjdm2.o: |- ._|_ = ( ocv ` W )
  assume pjdm2.s: |- .(+) = ( LSSum ` W )
  assume pjdm2.k: |- K = ( proj ` W )


  assert |- ( W e. PreHil -> ( T e. dom K <-> ( T e. L /\ ( T .(+) ( ._|_ ` T ) ) = V ) ) )

  proof
    cT
    cK
    cdm
    wcel
    cT
    cL
    wcel
    #
    cV
    cV
    cT
    cT
    c.pe
    cfv
    #
    cW
    cpj1
    cfv
    #
    co
    #
    wf
    #
    wa
    cW
    cphl
    wcel
    #
    @0
    cT
    @1
    c.po
    co
    #
    cV
    wceq
    #
    wa
    @2
    cT
    cK
    cL
    c.pe
    cV
    cW
    pjdm2.v
    pjdm2.l
    pjdm2.o
    @2
    eqid
    #
    pjdm2.k
    pjdm
    @5
    @0
    @4
    @7
    @5
    @0
    wa
    #
    @6
    cV
    @3
    wf
    #
    @4
    @7
    wb
    @9
    @6
    cT
    cV
    @3
    @9
    @2
    cW
    cplusg
    cfv
    #
    c.po
    cT
    @1
    cW
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    @11
    eqid
    pjdm2.s
    @12
    eqid
    #
    @13
    eqid
    #
    @9
    cL
    cW
    csubg
    cfv
    #
    cT
    @9
    cW
    clmod
    wcel
    #
    cL
    @16
    wss
    @5
    @17
    @0
    cW
    phllmod
    adantr
    #
    cL
    cW
    pjdm2.l
    lsssssubg
    syl
    #
    @5
    @0
    simpr
    sseldd
    #
    @9
    cL
    @16
    @1
    @19
    @0
    @5
    cT
    cV
    wss
    #
    @1
    cL
    wcel
    cL
    cT
    cV
    cW
    pjdm2.v
    pjdm2.l
    lssss
    #
    cT
    cL
    c.pe
    cV
    cW
    pjdm2.v
    pjdm2.o
    pjdm2.l
    ocvlss
    sylan2
    sseldd
    #
    cT
    cL
    c.pe
    cW
    @12
    pjdm2.o
    pjdm2.l
    @14
    ocvin
    @9
    cT
    @1
    cW
    @13
    @15
    @9
    @17
    cW
    cabl
    wcel
    @18
    cW
    lmodabl
    syl
    @20
    @23
    ablcntzd
    @8
    pj1f
    @0
    @21
    @5
    @22
    adantl
    fssd
    @10
    @4
    @7
    @10
    @6
    @3
    cdm
    #
    wceq
    @4
    @7
    @10
    @24
    @6
    @6
    cV
    @3
    fdm
    eqcomd
    @4
    @24
    cV
    @6
    cV
    cV
    @3
    fdm
    eqeq2d
    syl5ibcom
    @7
    @10
    @4
    @6
    cV
    cV
    @3
    feq2
    biimpcd
    impbid
    syl
    pm5.32da
    syl5bb
end
