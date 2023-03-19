include "cmt.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cxme.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "msxms.mm"
include "ressxms.mm"
include "sylan.mm"
include "cin.mm"
include "eqid.mm"
include "msmet.mm"
include "adantr.mm"
include "metres.mm"
include "syl.mm"
include "resres.mm"
include "inxp.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "wceq.mm"
include "ressds.mm"
include "adantl.mm"
include "incom.mm"
include "ressbas.mm"
include "syl5eq.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "ctopn.mm"
include "crest.mm"
include "resstopn.mm"
include "isms.mm"
include "sylanbrc.mm"

theorem ressms
  let cA: class A
  let cK: class K
  let cV: class V


  assert |- ( ( K e. MetSp /\ A e. V ) -> ( K |`s A ) e. MetSp )

  proof
    cK
    cmt
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cK
    cA
    cress
    co
    #
    cxme
    wcel
    #
    @3
    cds
    cfv
    #
    @3
    cbs
    cfv
    #
    @6
    cxp
    #
    cres
    #
    @6
    cme
    cfv
    #
    wcel
    @3
    cmt
    wcel
    @0
    cK
    cxme
    wcel
    @1
    @4
    cK
    msxms
    cA
    cK
    cV
    ressxms
    sylan
    @2
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @11
    cxp
    #
    cres
    #
    cA
    cA
    cxp
    #
    cres
    #
    @11
    cA
    cin
    #
    cme
    cfv
    #
    @8
    @9
    @2
    @13
    @11
    cme
    cfv
    wcel
    #
    @15
    @17
    wcel
    @0
    @18
    @1
    @13
    cK
    @11
    @11
    eqid
    #
    @13
    eqid
    msmet
    adantr
    @13
    cA
    @11
    metres
    syl
    @2
    @15
    @10
    @16
    @16
    cxp
    #
    cres
    #
    @8
    @15
    @10
    @12
    @14
    cin
    #
    cres
    @21
    @10
    @12
    @14
    resres
    @22
    @20
    @10
    @11
    @11
    cA
    cA
    inxp
    reseq2i
    eqtri
    @2
    @10
    @5
    @20
    @7
    @1
    @10
    @5
    wceq
    @0
    cA
    @10
    cK
    @3
    cV
    @3
    eqid
    #
    @10
    eqid
    ressds
    adantl
    @2
    @16
    @6
    @2
    @16
    cA
    @11
    cin
    #
    @6
    @11
    cA
    incom
    @1
    @24
    @6
    wceq
    @0
    cA
    @11
    @3
    cV
    cK
    @23
    @19
    ressbas
    adantl
    syl5eq
    #
    sqxpeqd
    reseq12d
    syl5eq
    @2
    @16
    @6
    cme
    @25
    fveq2d
    3eltr3d
    @8
    cK
    ctopn
    cfv
    #
    cA
    crest
    co
    @3
    @6
    cA
    @3
    @26
    cK
    @23
    @26
    eqid
    resstopn
    @6
    eqid
    @8
    eqid
    isms
    sylanbrc
end
