include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "wrex.mm"
include "wa.mm"
include "clsw.mm"
include "c0.mm"
include "wne.mm"
include "simp2.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0p1gt0.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "breq2.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "hashneq0.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "jca.mm"
include "adantr.mm"
include "lswcl.mm"
include "ccats1swrdeq.mm"
include "imp.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"

theorem ccats1swrdeqrex
  let cU: class U
  let cV: class V
  let cW: class W
  let vs: setvar s

  disjoint U s
  disjoint V s
  disjoint W s
  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U substr <. 0 , ( # ` W ) >. ) -> E. s e. V U = ( W ++ <" s "> ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cU
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cW
    cU
    cc0
    @4
    cop
    csubstr
    co
    wceq
    #
    cU
    cW
    vs
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    vs
    cV
    wrex
    #
    @7
    @8
    wa
    #
    cU
    clsw
    cfv
    #
    cV
    wcel
    #
    cU
    cW
    @15
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    wa
    @13
    @14
    @16
    @19
    @14
    @2
    cU
    c0
    wne
    #
    wa
    #
    @16
    @7
    @21
    @8
    @7
    @2
    @20
    @1
    @2
    @6
    simp2
    @7
    cc0
    @3
    clt
    wbr
    #
    @20
    @7
    @22
    cc0
    @5
    clt
    wbr
    #
    @1
    @2
    @23
    @6
    @1
    @4
    cn0
    wcel
    @23
    cV
    cW
    lencl
    @4
    nn0p1gt0
    syl
    3ad2ant1
    @6
    @1
    @22
    @23
    wb
    @2
    @3
    @5
    cc0
    clt
    breq2
    3ad2ant3
    mpbird
    @2
    @1
    @22
    @20
    wb
    @6
    cU
    @0
    hashneq0
    3ad2ant2
    mpbid
    jca
    adantr
    cV
    cU
    lswcl
    syl
    @7
    @8
    @19
    cU
    cV
    cW
    ccats1swrdeq
    imp
    jca
    @12
    @19
    vs
    @15
    cV
    @9
    @15
    wceq
    #
    @11
    @18
    cU
    @24
    @10
    @17
    cW
    cconcat
    @9
    @15
    s1eq
    oveq2d
    eqeq2d
    rspcev
    syl
    ex
end
