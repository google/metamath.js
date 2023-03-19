include "cxme.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "ctopn.mm"
include "crest.mm"
include "cmopn.mm"
include "wceq.mm"
include "cin.mm"
include "eqid.mm"
include "xmsxmet.mm"
include "adantr.mm"
include "xmetres.mm"
include "syl.mm"
include "resres.mm"
include "inxp.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "ressds.mm"
include "adantl.mm"
include "incom.mm"
include "ressbas.mm"
include "syl5eq.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "xmstopn.mm"
include "oveq1d.mm"
include "wss.mm"
include "inss1.mm"
include "xpss12.mm"
include "mp2an.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "metrest.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "cuni.mm"
include "ctps.mm"
include "xmstps.mm"
include "tpsuni.mm"
include "ineq2d.mm"
include "oveq2d.mm"
include "ctopon.mm"
include "istps.mm"
include "sylib.mm"
include "restin.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "resstopn.mm"
include "isxms2.mm"
include "sylanbrc.mm"

theorem ressxms
  let cA: class A
  let cK: class K
  let cV: class V


  assert |- ( ( K e. *MetSp /\ A e. V ) -> ( K |`s A ) e. *MetSp )

  proof
    cK
    cxme
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
    cds
    cfv
    #
    @3
    cbs
    cfv
    #
    @5
    cxp
    #
    cres
    #
    @5
    cxmt
    cfv
    #
    wcel
    cK
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    @7
    cmopn
    cfv
    #
    wceq
    @3
    cxme
    wcel
    @2
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @13
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
    @13
    cA
    cin
    #
    cxmt
    cfv
    #
    @7
    @8
    @2
    @15
    @13
    cxmt
    cfv
    wcel
    #
    @17
    @19
    wcel
    @0
    @20
    @1
    @15
    cK
    @13
    @13
    eqid
    #
    @15
    eqid
    #
    xmsxmet
    adantr
    #
    @15
    cA
    @13
    xmetres
    syl
    @2
    @17
    @12
    @18
    @18
    cxp
    #
    cres
    #
    @7
    @17
    @12
    @14
    @16
    cin
    #
    cres
    @25
    @12
    @14
    @16
    resres
    @26
    @24
    @12
    @13
    @13
    cA
    cA
    inxp
    reseq2i
    eqtri
    #
    @2
    @12
    @4
    @24
    @6
    @1
    @12
    @4
    wceq
    @0
    cA
    @12
    cK
    @3
    cV
    @3
    eqid
    #
    @12
    eqid
    ressds
    adantl
    @2
    @18
    @5
    @2
    @18
    cA
    @13
    cin
    #
    @5
    @13
    cA
    incom
    #
    @1
    @29
    @5
    wceq
    @0
    cA
    @13
    @3
    cV
    cK
    @28
    @21
    ressbas
    adantl
    syl5eq
    #
    sqxpeqd
    reseq12d
    syl5eq
    #
    @2
    @18
    @5
    cxmt
    @31
    fveq2d
    3eltr3d
    @2
    @9
    @18
    crest
    co
    #
    @17
    cmopn
    cfv
    #
    @10
    @11
    @2
    @33
    @15
    cmopn
    cfv
    #
    @18
    crest
    co
    #
    @34
    @2
    @9
    @35
    @18
    crest
    @0
    @9
    @35
    wceq
    @1
    @15
    @9
    cK
    @13
    @9
    eqid
    #
    @21
    @22
    xmstopn
    adantr
    oveq1d
    @2
    @20
    @18
    @13
    wss
    #
    @36
    @34
    wceq
    @23
    @13
    cA
    inss1
    #
    @15
    @17
    @35
    @34
    @13
    @18
    @17
    @25
    @15
    @24
    cres
    #
    @27
    @24
    @14
    wss
    #
    @40
    @25
    wceq
    @38
    @38
    @41
    @39
    @39
    @18
    @13
    @18
    @13
    xpss12
    mp2an
    @12
    @24
    @14
    resabs1
    ax-mp
    eqtr4i
    @35
    eqid
    @34
    eqid
    metrest
    sylancl
    eqtrd
    @2
    @33
    @9
    cA
    @9
    cuni
    #
    cin
    #
    crest
    co
    #
    @10
    @2
    @18
    @43
    @9
    crest
    @2
    @18
    @29
    @43
    @30
    @2
    @13
    @42
    cA
    @0
    @13
    @42
    wceq
    #
    @1
    @0
    cK
    ctps
    wcel
    #
    @45
    cK
    xmstps
    #
    @13
    @9
    cK
    @21
    @37
    tpsuni
    syl
    adantr
    ineq2d
    syl5eq
    oveq2d
    @0
    @9
    @13
    ctopon
    cfv
    #
    wcel
    #
    @1
    @10
    @44
    wceq
    @0
    @46
    @49
    @47
    @13
    @9
    cK
    @21
    @37
    istps
    sylib
    cA
    @9
    @48
    cV
    @42
    @42
    eqid
    restin
    sylan
    eqtr4d
    @2
    @17
    @7
    cmopn
    @32
    fveq2d
    3eqtr3d
    @7
    @10
    @3
    @5
    cA
    @3
    @9
    cK
    @28
    @37
    resstopn
    @5
    eqid
    @7
    eqid
    isxms2
    sylanbrc
end
