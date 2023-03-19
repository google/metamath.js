include "wcel.mm"
include "ccplgr.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "iscplgrnb.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "wb.mm"
include "df-3an.mm"
include "a1i.mm"
include "nbgrel.mm"
include "eldifsn.mm"
include "simpr.mm"
include "simpl.mm"
include "anim12ci.mm"
include "simprr.mm"
include "jca.mm"
include "sylan2b.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem iscplgredg
  let vv: setvar v
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume cplgruvtxb.v: |- V = ( Vtx ` G )
  assume iscplgredg.v: |- E = ( Edg ` G )

  disjoint G v
  disjoint V v
  disjoint G n
  disjoint n v
  disjoint V n
  disjoint W v
  disjoint E e
  disjoint G e
  disjoint V e
  disjoint W e
  disjoint W n
  disjoint e n
  disjoint e v
  disjoint G g
  disjoint V g
  disjoint g v
  disjoint W g
  assert |- ( G e. W -> ( G e. ComplGraph <-> A. v e. V A. n e. ( V \ { v } ) E. e e. E { v , n } C_ e ) )

  proof
    cG
    cW
    wcel
    #
    cG
    ccplgr
    wcel
    vn
    cv
    #
    cG
    vv
    cv
    #
    cnbgr
    co
    wcel
    #
    vn
    cV
    @2
    csn
    cdif
    #
    wral
    #
    vv
    cV
    wral
    @2
    @1
    cpr
    ve
    cv
    wss
    ve
    cE
    wrex
    #
    vn
    @4
    wral
    #
    vv
    cV
    wral
    vv
    vn
    cG
    cV
    cW
    cplgruvtxb.v
    iscplgrnb
    @0
    @5
    @7
    vv
    cV
    @0
    @2
    cV
    wcel
    #
    wa
    #
    @3
    @6
    vn
    @4
    @9
    @1
    @4
    wcel
    #
    wa
    #
    @1
    cV
    wcel
    #
    @8
    wa
    #
    @1
    @2
    wne
    #
    @6
    w3a
    #
    @13
    @14
    wa
    #
    @6
    wa
    #
    @3
    @6
    @15
    @17
    wb
    @11
    @13
    @14
    @6
    df-3an
    a1i
    @3
    @15
    wb
    @11
    ve
    cE
    cG
    @1
    cV
    @2
    cplgruvtxb.v
    iscplgredg.v
    nbgrel
    a1i
    @11
    @16
    @6
    @10
    @9
    @12
    @14
    wa
    #
    @16
    @1
    cV
    @2
    eldifsn
    @9
    @18
    wa
    @13
    @14
    @9
    @8
    @18
    @12
    @0
    @8
    simpr
    @12
    @14
    simpl
    anim12ci
    @9
    @12
    @14
    simprr
    jca
    sylan2b
    biantrurd
    3bitr4d
    ralbidva
    ralbidva
    bitrd
end
