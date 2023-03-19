include "cupgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "ciedg.mm"
include "crn.mm"
include "wceq.mm"
include "edgval.mm"
include "a1i.mm"
include "eleq2d.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "upgrf.mm"
include "frn.mm"
include "syl.mm"
include "sseld.mm"
include "wa.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "wi.mm"
include "eldifsn.mm"
include "biimpi.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "syl5bi.mm"
include "syld.mm"
include "sylbid.mm"
include "imp.mm"

theorem edgupgr
  let cE: class E
  let cG: class G
  let vx: setvar x


  assert |- ( ( G e. UPGraph /\ E e. ( Edg ` G ) ) -> ( E e. ~P ( Vtx ` G ) /\ E =/= (/) /\ ( # ` E ) <_ 2 ) )

  proof
    cG
    cupgr
    wcel
    #
    cE
    cG
    cedg
    cfv
    #
    wcel
    #
    cE
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    cE
    c0
    wne
    #
    cE
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    w3a
    #
    @0
    @2
    cE
    cG
    ciedg
    cfv
    #
    crn
    #
    wcel
    #
    @9
    @0
    @1
    @11
    cE
    @1
    @11
    wceq
    @0
    cG
    edgval
    a1i
    eleq2d
    @0
    @12
    cE
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    @4
    c0
    csn
    cdif
    #
    crab
    #
    wcel
    #
    @9
    @0
    @11
    @17
    cE
    @0
    @10
    cdm
    #
    @17
    @10
    wf
    @11
    @17
    wss
    vx
    @10
    cG
    @3
    @3
    eqid
    @10
    eqid
    upgrf
    @19
    @17
    @10
    frn
    syl
    sseld
    @18
    cE
    @16
    wcel
    #
    @8
    wa
    #
    @0
    @9
    @15
    @8
    vx
    cE
    @16
    @13
    cE
    wceq
    @14
    @7
    c2
    cle
    @13
    cE
    chash
    fveq2
    breq1d
    elrab
    @21
    @9
    wi
    @0
    @21
    @5
    @6
    wa
    #
    @8
    wa
    @9
    @20
    @22
    @8
    @20
    @22
    cE
    @4
    c0
    eldifsn
    biimpi
    anim1i
    @5
    @6
    @8
    df-3an
    sylibr
    a1i
    syl5bi
    syld
    sylbid
    imp
end
