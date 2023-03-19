include "crp.mm"
include "wcel.mm"
include "cpi.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cim.mm"
include "ccnv.mm"
include "cico.mm"
include "cima.mm"
include "cc.mm"
include "simpr.mm"
include "cxr.mm"
include "wceq.mm"
include "rpxr.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "cnbl0.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "simplbi.mm"
include "imcld.mm"
include "recnd.mm"
include "abscld.mm"
include "rpre.mm"
include "pire.mm"
include "a1i.mm"
include "cle.mm"
include "absimle.mm"
include "w3a.mm"
include "simprbi.mm"
include "0re.mm"
include "elico2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "lelttrd.mm"
include "simplr.mm"
include "lttrd.mm"

theorem efopnlem1
  let cA: class A
  let cR: class R


  assert |- ( ( ( R e. RR+ /\ R < _pi ) /\ A e. ( 0 ( ball ` ( abs o. - ) ) R ) ) -> ( abs ` ( Im ` A ) ) < _pi )

  proof
    cR
    crp
    wcel
    #
    cR
    cpi
    clt
    wbr
    #
    wa
    #
    cA
    cc0
    cR
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wcel
    #
    wa
    #
    cA
    cim
    cfv
    #
    cabs
    cfv
    #
    cR
    cpi
    @6
    @7
    @6
    @7
    @6
    cA
    @6
    cA
    cabs
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    wcel
    #
    cA
    cc
    wcel
    #
    @6
    cA
    @4
    @10
    @2
    @5
    simpr
    @6
    cR
    cxr
    wcel
    #
    @10
    @4
    wceq
    @0
    @13
    @1
    @5
    cR
    rpxr
    ad2antrr
    #
    @3
    cR
    @3
    eqid
    cnbl0
    syl
    eleqtrrd
    #
    @11
    @12
    cA
    cabs
    cfv
    #
    @9
    wcel
    #
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @11
    @12
    @17
    wa
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    cA
    @9
    cabs
    elpreima
    mp2b
    #
    simplbi
    syl
    #
    imcld
    recnd
    abscld
    #
    @0
    cR
    cr
    wcel
    @1
    @5
    cR
    rpre
    ad2antrr
    #
    cpi
    cr
    wcel
    @6
    pire
    a1i
    @6
    @8
    @16
    cR
    @20
    @6
    cA
    @19
    abscld
    @21
    @6
    @12
    @8
    @16
    cle
    wbr
    @19
    cA
    absimle
    syl
    @6
    @16
    cr
    wcel
    #
    cc0
    @16
    cle
    wbr
    #
    @16
    cR
    clt
    wbr
    #
    @6
    @17
    @22
    @23
    @24
    w3a
    #
    @6
    @11
    @17
    @15
    @11
    @12
    @17
    @18
    simprbi
    syl
    @6
    cc0
    cr
    wcel
    @13
    @17
    @25
    wb
    0re
    @14
    cc0
    cR
    @16
    elico2
    sylancr
    mpbid
    simp3d
    lelttrd
    @0
    @1
    @5
    simplr
    lttrd
end
