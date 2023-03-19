include "chl.mm"
include "wcel.mm"
include "cbn.mm"
include "ccph.mm"
include "wa.mm"
include "ccms.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "w3a.mm"
include "ishl.mm"
include "df-3an.mm"
include "3ancomb.mm"
include "cnvc.mm"
include "wb.mm"
include "cphnvc.mm"
include "isbn.mm"
include "3anass.mm"
include "bitri.mm"
include "baib.mm"
include "syl.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "cphsca.mm"
include "eleq1d.mm"
include "csubrg.mm"
include "cfv.mm"
include "cdr.mm"
include "wi.mm"
include "cphsubrg.mm"
include "clvec.mm"
include "cphlvec.mm"
include "lvecdrng.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "cncdrg.mm"
include "3expia.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wo.mm"
include "elpri.mm"
include "oveq2.mm"
include "ctopn.mm"
include "ccld.mm"
include "recld2.mm"
include "wss.mm"
include "cncms.mm"
include "ax-resscn.mm"
include "cnfldbas.mm"
include "cmsss.mm"
include "mp2an.mm"
include "mpbir.mm"
include "syl6eqel.mm"
include "ressid.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "jaoi.mm"
include "impbid1.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "pm5.32ri.mm"
include "3bitr4ri.mm"

theorem ishl2
  let cF: class F
  let cK: class K
  let cW: class W
  assume hlress.f: |- F = ( Scalar ` W )
  assume hlress.k: |- K = ( Base ` F )


  assert |- ( W e. CHil <-> ( W e. CMetSp /\ W e. CPreHil /\ K e. { RR , CC } ) )

  proof
    cW
    chl
    wcel
    cW
    cbn
    wcel
    #
    cW
    ccph
    wcel
    #
    wa
    #
    cW
    ccms
    wcel
    #
    @1
    cK
    cr
    cc
    cpr
    wcel
    #
    w3a
    #
    cW
    ishl
    @3
    @4
    @1
    w3a
    @3
    @4
    wa
    #
    @1
    wa
    @5
    @2
    @3
    @4
    @1
    df-3an
    @3
    @1
    @4
    3ancomb
    @1
    @0
    @6
    @1
    @0
    @3
    cF
    ccms
    wcel
    #
    wa
    #
    @6
    @1
    cW
    cnvc
    wcel
    #
    @0
    @8
    wb
    cW
    cphnvc
    @0
    @9
    @8
    @0
    @9
    @3
    @7
    w3a
    @9
    @8
    wa
    cF
    cW
    hlress.f
    isbn
    @9
    @3
    @7
    3anass
    bitri
    baib
    syl
    @1
    @7
    @4
    @3
    @1
    @7
    ccnfld
    cK
    cress
    co
    #
    ccms
    wcel
    #
    @4
    @1
    cF
    @10
    ccms
    cF
    cK
    cW
    hlress.f
    hlress.k
    cphsca
    #
    eleq1d
    @1
    @11
    @4
    @1
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    @10
    cdr
    wcel
    #
    @11
    @4
    wi
    cF
    cK
    cW
    hlress.f
    hlress.k
    cphsubrg
    @1
    cF
    @10
    cdr
    @12
    @1
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    cW
    cphlvec
    cF
    cW
    hlress.f
    lvecdrng
    syl
    eqeltrrd
    @13
    @14
    @11
    @4
    @10
    cK
    @10
    eqid
    cncdrg
    3expia
    syl2anc
    @4
    cK
    cr
    wceq
    #
    cK
    cc
    wceq
    #
    wo
    @11
    cK
    cr
    cc
    elpri
    @15
    @11
    @16
    @15
    @10
    ccnfld
    cr
    cress
    co
    #
    ccms
    cK
    cr
    ccnfld
    cress
    oveq2
    @17
    ccms
    wcel
    #
    cr
    ccnfld
    ctopn
    cfv
    #
    ccld
    cfv
    wcel
    #
    @19
    @19
    eqid
    #
    recld2
    ccnfld
    ccms
    wcel
    #
    cr
    cc
    wss
    @18
    @20
    wb
    cncms
    ax-resscn
    cr
    @19
    @17
    ccnfld
    cc
    @17
    eqid
    cnfldbas
    @21
    cmsss
    mp2an
    mpbir
    syl6eqel
    @16
    @10
    ccnfld
    cc
    cress
    co
    #
    ccms
    cK
    cc
    ccnfld
    cress
    oveq2
    @23
    ccnfld
    ccms
    @22
    @23
    ccnfld
    wceq
    cncms
    cc
    ccnfld
    ccms
    cnfldbas
    ressid
    ax-mp
    cncms
    eqeltri
    syl6eqel
    jaoi
    syl
    impbid1
    bitrd
    anbi2d
    bitrd
    pm5.32ri
    3bitr4ri
    bitri
end
