include "clvec.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "clss.mm"
include "cv.mm"
include "cun.mm"
include "clspn.mm"
include "wceq.mm"
include "wrex.mm"
include "clmod.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqid.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "simp3.mm"
include "wb.mm"
include "lkr0f.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "cur.mm"
include "lfl1.mm"
include "wn.mm"
include "simp11.mm"
include "simp12.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "drngunz.mm"
include "3syl.mm"
include "eqnetrd.mm"
include "wa.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpr.mm"
include "lkrf0.mm"
include "syl3anc.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "lkrlsp3.mm"
include "syl121anc.mm"
include "3expia.mm"
include "reximdva.mm"
include "islshp.mm"
include "mpbir3and.mm"

theorem lkrshp
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vv: setvar v
  assume lkrshp.v: |- V = ( Base ` W )
  assume lkrshp.d: |- D = ( Scalar ` W )
  assume lkrshp.z: |- .0. = ( 0g ` D )
  assume lkrshp.h: |- H = ( LSHyp ` W )
  assume lkrshp.f: |- F = ( LFnl ` W )
  assume lkrshp.k: |- K = ( LKer ` W )


  assert |- ( ( W e. LVec /\ G e. F /\ G =/= ( V X. { .0. } ) ) -> ( K ` G ) e. H )

  proof
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    cG
    cV
    c.0
    csn
    cxp
    #
    wne
    #
    w3a
    #
    cG
    cK
    cfv
    #
    cH
    wcel
    #
    @5
    cW
    clss
    cfv
    #
    wcel
    #
    @5
    cV
    wne
    #
    @5
    vv
    cv
    #
    csn
    cun
    cW
    clspn
    cfv
    #
    cfv
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    @4
    cW
    clmod
    wcel
    #
    @1
    @8
    @0
    @1
    @14
    @3
    cW
    lveclmod
    3ad2ant1
    #
    @0
    @1
    @3
    simp2
    #
    @7
    cF
    cG
    cK
    cW
    lkrshp.f
    lkrshp.k
    @7
    eqid
    #
    lkrlss
    syl2anc
    @4
    @9
    @3
    @0
    @1
    @3
    simp3
    @4
    @5
    cV
    cG
    @2
    @4
    @14
    @1
    @5
    cV
    wceq
    cG
    @2
    wceq
    wb
    @15
    @16
    cD
    cF
    cG
    cK
    cV
    cW
    c.0
    lkrshp.d
    lkrshp.z
    lkrshp.v
    lkrshp.f
    lkrshp.k
    lkr0f
    syl2anc
    necon3bid
    mpbird
    @4
    @10
    cG
    cfv
    #
    cD
    cur
    cfv
    #
    wceq
    #
    vv
    cV
    wrex
    @13
    vv
    cD
    @19
    cF
    cG
    cV
    cW
    c.0
    lkrshp.d
    lkrshp.z
    @19
    eqid
    #
    lkrshp.v
    lkrshp.f
    lfl1
    @4
    @20
    @12
    vv
    cV
    @4
    @10
    cV
    wcel
    #
    @20
    @12
    @4
    @22
    @20
    w3a
    #
    @0
    @22
    @1
    @10
    @5
    wcel
    #
    wn
    #
    @12
    @0
    @1
    @3
    @22
    @20
    simp11
    #
    @4
    @22
    @20
    simp2
    @0
    @1
    @3
    @22
    @20
    simp12
    @23
    @18
    c.0
    wne
    @25
    @23
    @18
    @19
    c.0
    @4
    @22
    @20
    simp3
    @23
    @0
    cD
    cdr
    wcel
    @19
    c.0
    wne
    @26
    cD
    cW
    lkrshp.d
    lvecdrng
    cD
    @19
    c.0
    lkrshp.z
    @21
    drngunz
    3syl
    eqnetrd
    @23
    @24
    @18
    c.0
    @23
    @24
    @18
    c.0
    wceq
    #
    @23
    @24
    wa
    @0
    @1
    @24
    @27
    @0
    @1
    @3
    @22
    @20
    @24
    simpl11
    @0
    @1
    @3
    @22
    @20
    @24
    simpl12
    @23
    @24
    simpr
    cD
    cF
    cG
    cK
    cW
    @10
    clvec
    c.0
    lkrshp.d
    lkrshp.z
    lkrshp.f
    lkrshp.k
    lkrf0
    syl3anc
    ex
    necon3ad
    mpd
    cF
    cG
    cK
    @11
    cV
    cW
    @10
    lkrshp.v
    @11
    eqid
    #
    lkrshp.f
    lkrshp.k
    lkrlsp3
    syl121anc
    3expia
    reximdva
    mpd
    @0
    @1
    @6
    @8
    @9
    @13
    w3a
    wb
    @3
    vv
    @7
    @5
    cH
    @11
    cV
    cW
    clvec
    lkrshp.v
    @28
    @17
    lkrshp.h
    islshp
    3ad2ant1
    mpbir3and
end
