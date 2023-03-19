include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cdr.mm"
include "ccms.mm"
include "w3a.mm"
include "cr.mm"
include "cq.mm"
include "ctopn.mm"
include "ccl.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctop.mm"
include "cc.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "ax-resscn.mm"
include "qssre.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "tgioo2.mm"
include "restcls.mm"
include "mp3an.mm"
include "qdensere.mm"
include "eqtr3i.mm"
include "sseqin2.mm"
include "mpbir.mm"
include "ccld.mm"
include "simp3.mm"
include "wb.mm"
include "cncms.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "3ad2ant1.mm"
include "cmsss.mm"
include "sylancr.mm"
include "mpbid.mm"
include "cress.mm"
include "co.mm"
include "eleq1i.mm"
include "qsssubdrg.mm"
include "sylan2b.mm"
include "3adant3.mm"
include "clsss2.mm"
include "syl2anc.mm"
include "syl5ss.mm"

theorem resscdrg
  let cF: class F
  let cK: class K
  assume resscdrg.1: |- F = ( CCfld |`s K )


  assert |- ( ( K e. ( SubRing ` CCfld ) /\ F e. DivRing /\ F e. CMetSp ) -> RR C_ K )

  proof
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cF
    cdr
    wcel
    #
    cF
    ccms
    wcel
    #
    w3a
    #
    cr
    cq
    ccnfld
    ctopn
    cfv
    #
    ccl
    cfv
    cfv
    #
    cK
    cr
    @5
    wss
    @5
    cr
    cin
    #
    cr
    wceq
    cq
    cioo
    crn
    ctg
    cfv
    #
    ccl
    cfv
    cfv
    #
    @6
    cr
    @4
    ctop
    wcel
    cr
    cc
    wss
    cq
    cr
    wss
    @8
    @6
    wceq
    @4
    @4
    eqid
    #
    cnfldtop
    ax-resscn
    qssre
    cq
    @4
    @7
    cc
    cr
    cc
    @4
    @4
    @9
    cnfldtopon
    toponunii
    #
    @4
    @9
    tgioo2
    restcls
    mp3an
    qdensere
    eqtr3i
    cr
    @5
    sseqin2
    mpbir
    @3
    cK
    @4
    ccld
    cfv
    wcel
    #
    cq
    cK
    wss
    #
    @5
    cK
    wss
    @3
    @2
    @11
    @0
    @1
    @2
    simp3
    @3
    ccnfld
    ccms
    wcel
    cK
    cc
    wss
    #
    @2
    @11
    wb
    cncms
    @0
    @1
    @13
    @2
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    3ad2ant1
    cK
    @4
    cF
    ccnfld
    cc
    resscdrg.1
    cnfldbas
    @9
    cmsss
    sylancr
    mpbid
    @0
    @1
    @12
    @2
    @1
    @0
    ccnfld
    cK
    cress
    co
    #
    cdr
    wcel
    @12
    cF
    @14
    cdr
    resscdrg.1
    eleq1i
    cK
    qsssubdrg
    sylan2b
    3adant3
    cK
    cq
    @4
    cc
    @10
    clsss2
    syl2anc
    syl5ss
end
