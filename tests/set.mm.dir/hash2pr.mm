include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "cpr.mm"
include "wex.mm"
include "cfn.mm"
include "cn0.mm"
include "wi.mm"
include "2nn0.mm"
include "hashvnfin.mm"
include "mpan2.mm"
include "imp.mm"
include "hash2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "wb.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "hashen.mm"
include "biimpd.mm"
include "sylbid.mm"
include "adantld.mm"
include "mpcom.mm"
include "en2.mm"
include "syl.mm"

theorem hash2pr
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint V a
  disjoint V b
  disjoint a b
  assert |- ( ( V e. W /\ ( # ` V ) = 2 ) -> E. a E. b V = { a , b } )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cV
    c2o
    cen
    wbr
    #
    cV
    va
    cv
    vb
    cv
    cpr
    wceq
    vb
    wex
    va
    wex
    cV
    cfn
    wcel
    #
    @3
    @4
    @0
    @2
    @5
    @0
    c2
    cn0
    wcel
    @2
    @5
    wi
    2nn0
    cV
    c2
    cW
    hashvnfin
    mpan2
    imp
    @5
    @2
    @4
    @0
    @5
    @2
    @1
    c2o
    chash
    cfv
    #
    wceq
    #
    @4
    @5
    c2
    @6
    @1
    c2
    @6
    wceq
    @5
    @6
    c2
    hash2
    eqcomi
    a1i
    eqeq2d
    @5
    @7
    @4
    @5
    c2o
    cfn
    wcel
    #
    @7
    @4
    wb
    c2o
    com
    wcel
    @8
    2onn
    c2o
    nnfi
    ax-mp
    cV
    c2o
    hashen
    mpan2
    biimpd
    sylbid
    adantld
    mpcom
    va
    vb
    cV
    en2
    syl
end
