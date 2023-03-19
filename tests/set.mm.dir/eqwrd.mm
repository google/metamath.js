include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "wrdfn.mm"
include "eqfnfv2.mm"
include "syl2an.mm"
include "fveq2.mm"
include "cn0.mm"
include "lencl.mm"
include "hashfzo0.mm"
include "syl.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "oveq2.mm"
include "impbid1.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem eqwrd
  let cU: class U
  let vi: setvar i
  let cV: class V
  let cW: class W

  disjoint U i
  disjoint W i
  assert |- ( ( U e. Word V /\ W e. Word V ) -> ( U = W <-> ( ( # ` U ) = ( # ` W ) /\ A. i e. ( 0 ..^ ( # ` U ) ) ( U ` i ) = ( W ` i ) ) ) )

  proof
    cU
    cV
    cword
    #
    wcel
    #
    cW
    @0
    wcel
    #
    wa
    #
    cU
    cW
    wceq
    #
    cc0
    cU
    chash
    cfv
    #
    cfzo
    co
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wceq
    #
    vi
    cv
    #
    cU
    cfv
    @10
    cW
    cfv
    wceq
    vi
    @6
    wral
    #
    wa
    #
    @5
    @7
    wceq
    #
    @11
    wa
    @1
    cU
    @6
    wfn
    cW
    @8
    wfn
    @4
    @12
    wb
    @2
    cV
    cU
    wrdfn
    cV
    cW
    wrdfn
    vi
    @6
    @8
    cU
    cW
    eqfnfv2
    syl2an
    @3
    @9
    @13
    @11
    @3
    @9
    @13
    @9
    @6
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    wceq
    @3
    @13
    @6
    @8
    chash
    fveq2
    @1
    @2
    @14
    @5
    @15
    @7
    @1
    @5
    cn0
    wcel
    @14
    @5
    wceq
    cV
    cU
    lencl
    @5
    hashfzo0
    syl
    @2
    @7
    cn0
    wcel
    @15
    @7
    wceq
    cV
    cW
    lencl
    @7
    hashfzo0
    syl
    eqeqan12d
    syl5ib
    @5
    @7
    cc0
    cfzo
    oveq2
    impbid1
    anbi1d
    bitrd
end
