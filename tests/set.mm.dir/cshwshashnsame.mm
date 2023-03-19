include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cprime.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cfzo.mm"
include "co.mm"
include "wrex.mm"
include "wceq.mm"
include "ccsh.mm"
include "csn.mm"
include "ciun.mm"
include "csu.mm"
include "cshwsiun.mm"
include "ad2antrr.mm"
include "fveq2d.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "snfi.mm"
include "id.mm"
include "cshwsdisj.mm"
include "hashiun.mm"
include "c1.mm"
include "cvv.mm"
include "ovex.mm"
include "hashsng.mm"
include "mp1i.mm"
include "sumeq2sdv.mm"
include "cmul.mm"
include "cc.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "sylancr.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "hashfzo0.mm"
include "syl.mm"
include "oveq1d.mm"
include "cr.mm"
include "prmnn.mm"
include "nnred.mm"
include "adantl.mm"
include "ax-1rid.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "ex.mm"

theorem cshwshashnsame
  let vw: setvar w
  let vi: setvar i
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cW: class W
  let cA: class A
  let vu: setvar u
  let vr: setvar r
  let cN: class N
  assume cshwrepswhash1.m: |- M = { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w }

  disjoint V n
  disjoint V w
  disjoint n w
  disjoint W n
  disjoint W w
  disjoint i n
  disjoint i w
  disjoint W i
  disjoint V i
  disjoint A i
  disjoint A n
  disjoint A u
  disjoint A w
  disjoint i u
  disjoint n u
  disjoint u w
  disjoint M r
  disjoint N i
  disjoint N n
  disjoint N u
  disjoint N w
  disjoint V r
  disjoint V u
  disjoint n r
  disjoint r u
  disjoint r w
  disjoint W r
  disjoint W u
  disjoint i r
  assert |- ( ( W e. Word V /\ ( # ` W ) e. Prime ) -> ( E. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) =/= ( W ` 0 ) -> ( # ` M ) = ( # ` W ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cprime
    wcel
    #
    wa
    #
    vi
    cv
    cW
    cfv
    cc0
    cW
    cfv
    wne
    vi
    cc0
    @1
    cfzo
    co
    #
    wrex
    #
    cM
    chash
    cfv
    #
    @1
    wceq
    @3
    @5
    wa
    #
    @6
    vn
    @4
    cW
    vn
    cv
    #
    ccsh
    co
    #
    csn
    #
    ciun
    #
    chash
    cfv
    @4
    @10
    chash
    cfv
    #
    vn
    csu
    #
    @1
    @7
    cM
    @11
    chash
    @0
    cM
    @11
    wceq
    @2
    @5
    vw
    vn
    cM
    cV
    cW
    cshwrepswhash1.m
    cshwsiun
    ad2antrr
    fveq2d
    @7
    vn
    @4
    @10
    @4
    cfn
    wcel
    #
    @7
    cc0
    @1
    fzofi
    #
    a1i
    @10
    cfn
    wcel
    @7
    @8
    @4
    wcel
    wa
    @9
    snfi
    a1i
    @3
    vi
    vn
    cV
    cW
    @3
    id
    cshwsdisj
    hashiun
    @7
    @13
    @4
    c1
    vn
    csu
    #
    @1
    @7
    @4
    @12
    c1
    vn
    @9
    cvv
    wcel
    @12
    c1
    wceq
    @7
    cW
    @8
    ccsh
    ovex
    @9
    cvv
    hashsng
    mp1i
    sumeq2sdv
    @3
    @16
    @1
    wceq
    @5
    @3
    @16
    @4
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @1
    c1
    cmul
    co
    #
    @1
    @3
    @14
    c1
    cc
    wcel
    @16
    @18
    wceq
    @15
    @3
    1cnd
    @4
    c1
    vn
    fsumconst
    sylancr
    @3
    @17
    @1
    c1
    cmul
    @3
    @1
    cn0
    wcel
    #
    @17
    @1
    wceq
    @0
    @20
    @2
    cV
    cW
    lencl
    adantr
    @1
    hashfzo0
    syl
    oveq1d
    @3
    @1
    cr
    wcel
    #
    @19
    @1
    wceq
    @2
    @21
    @0
    @2
    @1
    @1
    prmnn
    nnred
    adantl
    @1
    ax-1rid
    syl
    3eqtrd
    adantr
    eqtrd
    3eqtrd
    ex
end
