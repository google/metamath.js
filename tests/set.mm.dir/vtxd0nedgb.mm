include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "cxad.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "cvtxdg.mm"
include "fveq1i.mm"
include "eqid.mm"
include "vtxdgval.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "cxnn0.mm"
include "wb.mm"
include "cvv.mm"
include "ciedg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "dmex.mm"
include "rabex.mm"
include "hashxnn0.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "xnn0xadd0.mm"
include "mp1i.mm"
include "wo.mm"
include "c0.mm"
include "wral.mm"
include "hasheq0.mm"
include "anbi12i.mm"
include "rabeq0.mm"
include "ralnex.mm"
include "bicomi.mm"
include "ioran.mm"
include "ralbii.mm"
include "r19.26.mm"
include "3bitri.mm"
include "wi.mm"
include "snidg.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "pm4.72.mm"
include "sylib.mm"
include "orcom.mm"
include "syl6rbbr.mm"
include "rexbidv.mm"
include "notbid.mm"
include "syl5bb.mm"
include "3bitrd.mm"

theorem vtxd0nedgb
  let cD: class D
  let cU: class U
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cV: class V
  assume vtxd0nedgb.v: |- V = ( Vtx ` G )
  assume vtxd0nedgb.i: |- I = ( iEdg ` G )
  assume vtxd0nedgb.d: |- D = ( VtxDeg ` G )

  disjoint G i
  disjoint I i
  disjoint U i
  disjoint V i
  assert |- ( U e. V -> ( ( D ` U ) = 0 <-> -. E. i e. dom I U e. ( I ` i ) ) )

  proof
    cU
    cV
    wcel
    #
    cU
    cD
    cfv
    #
    cc0
    wceq
    cU
    vi
    cv
    cI
    cfv
    #
    wcel
    #
    vi
    cI
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @2
    cU
    csn
    #
    wceq
    #
    vi
    @4
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cc0
    wceq
    #
    @6
    cc0
    wceq
    #
    @10
    cc0
    wceq
    #
    wa
    #
    @3
    vi
    @4
    wrex
    #
    wn
    #
    @0
    @1
    @11
    cc0
    @0
    @1
    cU
    cG
    cvtxdg
    cfv
    #
    cfv
    @11
    cU
    cD
    @18
    vtxd0nedgb.d
    fveq1i
    vi
    @4
    cU
    cG
    cI
    cV
    vtxd0nedgb.v
    vtxd0nedgb.i
    @4
    eqid
    vtxdgval
    syl5eq
    eqeq1d
    @6
    cxnn0
    wcel
    #
    @10
    cxnn0
    wcel
    #
    wa
    @12
    @15
    wb
    @0
    @19
    @20
    @5
    cvv
    wcel
    #
    @19
    @3
    vi
    @4
    cI
    cI
    cG
    ciedg
    cfv
    cvv
    vtxd0nedgb.i
    cG
    ciedg
    fvex
    eqeltri
    dmex
    #
    rabex
    #
    @5
    cvv
    hashxnn0
    ax-mp
    @9
    cvv
    wcel
    #
    @20
    @8
    vi
    @4
    @22
    rabex
    #
    @9
    cvv
    hashxnn0
    ax-mp
    pm3.2i
    @6
    @10
    xnn0xadd0
    mp1i
    @15
    @3
    @8
    wo
    #
    vi
    @4
    wrex
    #
    wn
    #
    @0
    @17
    @15
    @5
    c0
    wceq
    #
    @9
    c0
    wceq
    #
    wa
    @3
    wn
    #
    vi
    @4
    wral
    #
    @8
    wn
    #
    vi
    @4
    wral
    #
    wa
    #
    @28
    @13
    @29
    @14
    @30
    @21
    @13
    @29
    wb
    @23
    @5
    cvv
    hasheq0
    ax-mp
    @24
    @14
    @30
    wb
    @25
    @9
    cvv
    hasheq0
    ax-mp
    anbi12i
    @29
    @32
    @30
    @34
    @3
    vi
    @4
    rabeq0
    @8
    vi
    @4
    rabeq0
    anbi12i
    @28
    @35
    @28
    @26
    wn
    #
    vi
    @4
    wral
    #
    @31
    @33
    wa
    #
    vi
    @4
    wral
    @35
    @37
    @28
    @26
    vi
    @4
    ralnex
    bicomi
    @36
    @38
    vi
    @4
    @3
    @8
    ioran
    ralbii
    @31
    @33
    vi
    @4
    r19.26
    3bitri
    bicomi
    3bitri
    @0
    @27
    @16
    @0
    @26
    @3
    vi
    @4
    @0
    @3
    @8
    @3
    wo
    #
    @26
    @0
    @8
    @3
    wi
    @3
    @39
    wb
    @0
    @3
    @8
    cU
    @7
    wcel
    cU
    cV
    snidg
    @2
    @7
    cU
    eleq2
    syl5ibrcom
    @8
    @3
    pm4.72
    sylib
    @3
    @8
    orcom
    syl6rbbr
    rexbidv
    notbid
    syl5bb
    3bitrd
end
