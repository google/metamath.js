include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "crn.mm"
include "cpw.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "simpr.mm"
include "eldifi.mm"
include "prelpwi.mm"
include "syl2an.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "adantl.mm"
include "wb.mm"
include "hashprg.mm"
include "mpbid.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "crab.mm"
include "rnresi.mm"
include "eqtri.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "sseq2.mm"
include "ssid.mm"
include "a1i.mm"
include "rspcedvd.mm"

theorem cusgrexilem2
  let vx: setvar x
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vn: setvar n
  let cV: class V
  let cW: class W
  assume usgrexi.p: |- P = { x e. ~P V | ( # ` x ) = 2 }

  disjoint V x
  disjoint P x
  disjoint W x
  disjoint P e
  disjoint P n
  disjoint P v
  disjoint e n
  disjoint e v
  disjoint e x
  disjoint n v
  disjoint n x
  disjoint v x
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint W e
  disjoint W n
  disjoint W v
  assert |- ( ( ( V e. W /\ v e. V ) /\ n e. ( V \ { v } ) ) -> E. e e. ran ( _I |` P ) { v , n } C_ e )

  proof
    cV
    cW
    wcel
    #
    vv
    cv
    #
    cV
    wcel
    #
    wa
    #
    vn
    cv
    #
    cV
    @1
    csn
    #
    cdif
    wcel
    #
    wa
    #
    @1
    @4
    cpr
    #
    ve
    cv
    #
    wss
    #
    @8
    @8
    wss
    #
    ve
    @8
    cid
    cP
    cres
    crn
    #
    @7
    @8
    cV
    cpw
    #
    wcel
    #
    @8
    chash
    cfv
    #
    c2
    wceq
    #
    @8
    @12
    wcel
    @3
    @2
    @4
    cV
    wcel
    #
    @14
    @6
    @0
    @2
    simpr
    #
    @4
    cV
    @5
    eldifi
    #
    @1
    @4
    cV
    prelpwi
    syl2an
    @7
    @1
    @4
    wne
    #
    @16
    @6
    @20
    @3
    @6
    @4
    @1
    @4
    cV
    @1
    eldifsni
    necomd
    adantl
    @3
    @2
    @17
    @20
    @16
    wb
    @6
    @18
    @19
    @1
    @4
    cV
    cV
    hashprg
    syl2an
    mpbid
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    @16
    vx
    @8
    @13
    @12
    @21
    @8
    wceq
    @22
    @15
    c2
    @21
    @8
    chash
    fveq2
    eqeq1d
    @12
    cP
    @23
    vx
    @13
    crab
    cP
    rnresi
    usgrexi.p
    eqtri
    elrab2
    sylanbrc
    @9
    @8
    wceq
    @10
    @11
    wb
    @7
    @9
    @8
    @8
    sseq2
    adantl
    @11
    @7
    @8
    ssid
    a1i
    rspcedvd
end
