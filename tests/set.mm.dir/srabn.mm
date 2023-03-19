include "cnrg.mm"
include "wcel.mm"
include "ccms.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cbn.mm"
include "csca.mm"
include "cnvc.mm"
include "wa.mm"
include "ccld.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "wb.mm"
include "simp2.mm"
include "cbs.mm"
include "eqidd.mm"
include "csra.mm"
include "wceq.mm"
include "a1i.mm"
include "wss.mm"
include "eqid.mm"
include "subrgss.mm"
include "3ad2ant3.mm"
include "srabase.mm"
include "cds.mm"
include "cxp.mm"
include "srads.mm"
include "reseq1d.mm"
include "sratopn.mm"
include "cmspropd.mm"
include "mpbid.mm"
include "isbn.mm"
include "3anrot.mm"
include "3anass.mm"
include "3bitri.mm"
include "baib.mm"
include "syl.mm"
include "srasca.mm"
include "eleq1d.mm"
include "cmsss.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "cnlm.mm"
include "sranlm.mm"
include "3adant2.mm"
include "isnvc2.mm"
include "bitr4d.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem srabn
  let cA: class A
  let cS: class S
  let cJ: class J
  let cW: class W
  assume srabn.a: |- A = ( ( subringAlg ` W ) ` S )
  assume srabn.j: |- J = ( TopOpen ` W )


  assert |- ( ( W e. NrmRing /\ W e. CMetSp /\ S e. ( SubRing ` W ) ) -> ( A e. Ban <-> ( S e. ( Clsd ` J ) /\ ( W |`s S ) e. DivRing ) ) )

  proof
    cW
    cnrg
    wcel
    #
    cW
    ccms
    wcel
    #
    cS
    cW
    csubrg
    cfv
    wcel
    #
    w3a
    #
    cA
    cbn
    wcel
    #
    cA
    csca
    cfv
    #
    ccms
    wcel
    #
    cA
    cnvc
    wcel
    #
    wa
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cW
    cS
    cress
    co
    #
    cdr
    wcel
    #
    wa
    @3
    cA
    ccms
    wcel
    #
    @4
    @8
    wb
    @3
    @1
    @12
    @0
    @1
    @2
    simp2
    #
    @3
    cW
    cbs
    cfv
    #
    cW
    cA
    @3
    @14
    eqidd
    @3
    cA
    cS
    cW
    cA
    cS
    cW
    csra
    cfv
    cfv
    wceq
    @3
    srabn.a
    a1i
    #
    @2
    @0
    cS
    @14
    wss
    #
    @1
    cS
    @14
    cW
    @14
    eqid
    #
    subrgss
    3ad2ant3
    #
    srabase
    @3
    cW
    cds
    cfv
    cA
    cds
    cfv
    @14
    @14
    cxp
    @3
    cA
    cS
    cW
    @15
    @18
    srads
    reseq1d
    @3
    cA
    cS
    cW
    @15
    @18
    sratopn
    cmspropd
    mpbid
    @4
    @12
    @8
    @4
    @7
    @12
    @6
    w3a
    @12
    @6
    @7
    w3a
    @12
    @8
    wa
    @5
    cA
    @5
    eqid
    #
    isbn
    @7
    @12
    @6
    3anrot
    @12
    @6
    @7
    3anass
    3bitri
    baib
    syl
    @3
    @6
    @9
    @7
    @11
    @3
    @10
    ccms
    wcel
    #
    @6
    @9
    @3
    @10
    @5
    ccms
    @3
    cA
    cS
    cW
    @15
    @18
    srasca
    #
    eleq1d
    @3
    @1
    @16
    @20
    @9
    wb
    @13
    @18
    cS
    cJ
    @10
    cW
    @14
    @10
    eqid
    @17
    srabn.j
    cmsss
    syl2anc
    bitr3d
    @3
    @7
    @5
    cdr
    wcel
    #
    @11
    @3
    cA
    cnlm
    wcel
    #
    @7
    @22
    wb
    @0
    @2
    @23
    @1
    cA
    cS
    cW
    srabn.a
    sranlm
    3adant2
    @7
    @23
    @22
    @5
    cA
    @19
    isnvc2
    baib
    syl
    @3
    @10
    @5
    cdr
    @21
    eleq1d
    bitr4d
    anbi12d
    bitrd
end
