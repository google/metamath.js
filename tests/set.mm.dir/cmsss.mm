include "ccms.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "cmopn.mm"
include "ccld.mm"
include "simpr.mm"
include "xpss12.mm"
include "sylancom.mm"
include "resabs1d.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "adantl.mm"
include "eqid.mm"
include "ressds.mm"
include "syl.mm"
include "ressbas2.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "wb.mm"
include "cmscmet.mm"
include "adantr.mm"
include "cmetss.mm"
include "bitr3d.mm"
include "cmt.mm"
include "cmsms.mm"
include "cress.mm"
include "co.mm"
include "ressms.mm"
include "syl5eqel.mm"
include "syl2an.mm"
include "iscms.mm"
include "baib.mm"
include "mstopn.mm"
include "eleq2d.mm"
include "3bitr4d.mm"

theorem cmsss
  let cA: class A
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  assume cmsss.h: |- K = ( M |`s A )
  assume cmsss.x: |- X = ( Base ` M )
  assume cmsss.j: |- J = ( TopOpen ` M )


  assert |- ( ( M e. CMetSp /\ A C_ X ) -> ( K e. CMetSp <-> A e. ( Clsd ` J ) ) )

  proof
    cM
    ccms
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @4
    cxp
    #
    cres
    #
    @4
    cms
    cfv
    #
    wcel
    #
    cA
    cM
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    ccld
    cfv
    #
    wcel
    #
    cK
    ccms
    wcel
    #
    cA
    cJ
    ccld
    cfv
    #
    wcel
    @2
    @11
    cA
    cA
    cxp
    #
    cres
    #
    cA
    cms
    cfv
    #
    wcel
    #
    @8
    @14
    @2
    @18
    @6
    @19
    @7
    @2
    @18
    @9
    @17
    cres
    @6
    @2
    @9
    @17
    @10
    @0
    @1
    @1
    @17
    @10
    wss
    @0
    @1
    simpr
    cA
    cX
    cA
    cX
    xpss12
    sylancom
    resabs1d
    @2
    @9
    @3
    @17
    @5
    @2
    cA
    cvv
    wcel
    #
    @9
    @3
    wceq
    @1
    @21
    @0
    cA
    cX
    cX
    cM
    cbs
    cfv
    cvv
    cmsss.x
    cM
    cbs
    fvex
    eqeltri
    ssex
    #
    adantl
    cA
    @9
    cM
    cK
    cvv
    cmsss.h
    @9
    eqid
    ressds
    syl
    @2
    cA
    @4
    @1
    cA
    @4
    wceq
    @0
    cA
    cX
    cK
    cM
    cmsss.h
    cmsss.x
    ressbas2
    adantl
    #
    sqxpeqd
    reseq12d
    eqtrd
    @2
    cA
    @4
    cms
    @23
    fveq2d
    eleq12d
    @2
    @11
    cX
    cms
    cfv
    wcel
    #
    @20
    @14
    wb
    @0
    @24
    @1
    @11
    cM
    cX
    cmsss.x
    @11
    eqid
    #
    cmscmet
    adantr
    @11
    @12
    cX
    cA
    @12
    eqid
    cmetss
    syl
    bitr3d
    @2
    cK
    cmt
    wcel
    #
    @15
    @8
    wb
    @0
    cM
    cmt
    wcel
    #
    @21
    @26
    @1
    cM
    cmsms
    #
    @22
    @27
    @21
    wa
    cK
    cM
    cA
    cress
    co
    cmt
    cmsss.h
    cA
    cM
    cvv
    ressms
    syl5eqel
    syl2an
    @15
    @26
    @8
    @6
    cK
    @4
    @4
    eqid
    @6
    eqid
    iscms
    baib
    syl
    @2
    @16
    @13
    cA
    @2
    cJ
    @12
    ccld
    @2
    @27
    cJ
    @12
    wceq
    @0
    @27
    @1
    @28
    adantr
    @11
    cJ
    cM
    cX
    cmsss.j
    cmsss.x
    @25
    mstopn
    syl
    fveq2d
    eleq2d
    3bitr4d
end
