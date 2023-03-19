include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "c3o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "ctp.mm"
include "wex.mm"
include "cfn.mm"
include "cn0.mm"
include "wi.mm"
include "3nn0.mm"
include "hashvnfin.mm"
include "mpan2.mm"
include "imp.mm"
include "hash3.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "wb.mm"
include "com.mm"
include "3onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "hashen.mm"
include "biimpd.mm"
include "sylbid.mm"
include "adantld.mm"
include "mpcom.mm"
include "en3.mm"
include "syl.mm"

theorem hash3tr
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint V a
  disjoint V b
  disjoint V c
  disjoint a b
  disjoint a c
  disjoint b c
  assert |- ( ( V e. W /\ ( # ` V ) = 3 ) -> E. a E. b E. c V = { a , b , c } )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    c3
    wceq
    #
    wa
    #
    cV
    c3o
    cen
    wbr
    #
    cV
    va
    cv
    vb
    cv
    vc
    cv
    ctp
    wceq
    vc
    wex
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
    c3
    cn0
    wcel
    @2
    @5
    wi
    3nn0
    cV
    c3
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
    c3o
    chash
    cfv
    #
    wceq
    #
    @4
    @5
    c3
    @6
    @1
    c3
    @6
    wceq
    @5
    @6
    c3
    hash3
    eqcomi
    a1i
    eqeq2d
    @5
    @7
    @4
    @5
    c3o
    cfn
    wcel
    #
    @7
    @4
    wb
    c3o
    com
    wcel
    @8
    3onn
    c3o
    nnfi
    ax-mp
    cV
    c3o
    hashen
    mpan2
    biimpd
    sylbid
    adantld
    mpcom
    va
    vb
    vc
    cV
    en3
    syl
end
