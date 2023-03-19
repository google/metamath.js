include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "ciedg.mm"
include "cdm.mm"
include "cvtx.mm"
include "wf1.mm"
include "cusgr.mm"
include "isausgr.mm"
include "wf1o.mm"
include "wi.mm"
include "f1oi.mm"
include "crn.mm"
include "dff1o5.mm"
include "f1ss.mm"
include "wb.mm"
include "dmresi.mm"
include "eqcomi.mm"
include "f1eq2.mm"
include "ax-mp.mm"
include "sylib.mm"
include "ex.mm"
include "a1d.mm"
include "adantr.mm"
include "sylbi.mm"
include "wf.mm"
include "wfn.mm"
include "df-f.mm"
include "rnresi.mm"
include "sseq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "f1f.mm"
include "syl11.mm"
include "impbid.mm"
include "cvv.mm"
include "resiexg.mm"
include "opiedgfv.mm"
include "sylan2.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "f1eq123d.mm"
include "bitr4d.mm"
include "opex.mm"
include "eqid.mm"
include "isusgrs.mm"
include "bicomi.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem ausgrusgrb
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ausgr.1: |- G = { <. v , e >. | e C_ { x e. ~P v | ( # ` x ) = 2 } }

  disjoint e v
  disjoint e x
  disjoint E e
  disjoint v x
  disjoint E v
  disjoint E x
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( V e. X /\ E e. Y ) -> ( V G E <-> <. V , ( _I |` E ) >. e. USGraph ) )

  proof
    cV
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    wa
    #
    cV
    cE
    cG
    wbr
    cE
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    wss
    #
    cV
    cid
    cE
    cres
    #
    cop
    #
    ciedg
    cfv
    #
    cdm
    #
    @3
    vx
    @8
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @9
    wf1
    #
    @8
    cusgr
    wcel
    #
    vx
    vv
    ve
    cE
    cG
    cV
    cX
    cY
    ausgr.1
    isausgr
    @2
    @6
    @7
    cdm
    #
    @5
    @7
    wf1
    #
    @14
    @2
    @6
    @17
    cE
    cE
    @7
    wf1o
    #
    @2
    @6
    @17
    wi
    #
    wi
    #
    cE
    f1oi
    @18
    cE
    cE
    @7
    wf1
    #
    @7
    crn
    #
    cE
    wceq
    #
    wa
    @20
    cE
    cE
    @7
    dff1o5
    @21
    @20
    @23
    @21
    @19
    @2
    @21
    @6
    @17
    @21
    @6
    wa
    cE
    @5
    @7
    wf1
    #
    @17
    cE
    cE
    @5
    @7
    f1ss
    cE
    @16
    wceq
    @24
    @17
    wb
    @16
    cE
    cE
    dmresi
    eqcomi
    cE
    @16
    @5
    @7
    f1eq2
    ax-mp
    sylib
    ex
    a1d
    adantr
    sylbi
    ax-mp
    @16
    @5
    @7
    wf
    #
    @2
    @6
    @17
    @25
    @7
    @16
    wfn
    #
    @22
    @5
    wss
    #
    wa
    @2
    @6
    wi
    #
    @16
    @5
    @7
    df-f
    @27
    @28
    @26
    @27
    @6
    @2
    @27
    @6
    @22
    cE
    @5
    cE
    rnresi
    sseq1i
    biimpi
    a1d
    adantl
    sylbi
    @16
    @5
    @7
    f1f
    syl11
    impbid
    @2
    @10
    @16
    @13
    @5
    @9
    @7
    @1
    @0
    @7
    cvv
    wcel
    #
    @9
    @7
    wceq
    cE
    cY
    resiexg
    #
    @7
    cV
    cX
    cvv
    opiedgfv
    sylan2
    #
    @2
    @9
    @7
    @31
    dmeqd
    @2
    @3
    vx
    @12
    @4
    @2
    @11
    cV
    @1
    @0
    @29
    @11
    cV
    wceq
    @30
    @7
    cV
    cX
    cvv
    opvtxfv
    sylan2
    pweqd
    rabeqdv
    f1eq123d
    bitr4d
    @14
    @15
    wb
    @2
    @15
    @14
    @8
    cvv
    wcel
    @15
    @14
    wb
    cV
    @7
    opex
    vx
    cvv
    @9
    @8
    @11
    @11
    eqid
    @9
    eqid
    isusgrs
    ax-mp
    bicomi
    a1i
    3bitrd
end
