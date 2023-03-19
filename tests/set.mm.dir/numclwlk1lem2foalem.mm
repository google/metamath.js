include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "c3.mm"
include "cuz.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "simpl.mm"
include "s1cl.mm"
include "3anim123i.mm"
include "3expb.mm"
include "ccatass.mm"
include "syl.mm"
include "oveq1d.mm"
include "adantr.mm"
include "ccat2s1cl.mm"
include "adantl.mm"
include "simpr.mm"
include "eqcomd.mm"
include "swrdccatid.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "3adant3.mm"
include "caddc.mm"
include "1e2m1.mm"
include "oveq2i.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "syl5eq.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "ccatw2s1p2.mm"
include "ccatw2s1p1.mm"
include "3jca.mm"

theorem numclwlk1lem2foalem
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( W e. Word V /\ ( # ` W ) = ( N - 2 ) ) /\ ( X e. V /\ Y e. V ) /\ N e. ( ZZ>= ` 3 ) ) -> ( ( ( ( W ++ <" X "> ) ++ <" Y "> ) substr <. 0 , ( N - 2 ) >. ) = W /\ ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` ( N - 1 ) ) = Y /\ ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` ( N - 2 ) ) = X ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c2
    cmin
    co
    #
    wceq
    #
    wa
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cW
    cX
    cs1
    #
    cconcat
    co
    cY
    cs1
    #
    cconcat
    co
    #
    cc0
    @3
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    cN
    c1
    cmin
    co
    #
    @13
    cfv
    #
    cY
    wceq
    @3
    @13
    cfv
    cX
    wceq
    #
    @5
    @8
    @16
    @9
    @5
    @8
    wa
    #
    @15
    cW
    @11
    @12
    cconcat
    co
    #
    cconcat
    co
    #
    @14
    csubstr
    co
    #
    cW
    @20
    @13
    @22
    @14
    csubstr
    @20
    @1
    @11
    @0
    wcel
    #
    @12
    @0
    wcel
    #
    w3a
    #
    @13
    @22
    wceq
    @5
    @6
    @7
    @26
    @5
    @1
    @6
    @24
    @7
    @25
    @1
    @4
    simpl
    #
    cX
    cV
    s1cl
    cY
    cV
    s1cl
    3anim123i
    3expb
    cV
    cW
    @11
    @12
    ccatass
    syl
    oveq1d
    @20
    @1
    @21
    @0
    wcel
    #
    @3
    @2
    wceq
    #
    @23
    cW
    wceq
    @5
    @1
    @8
    @27
    adantr
    @8
    @28
    @5
    cV
    cX
    cY
    ccat2s1cl
    adantl
    @5
    @29
    @8
    @5
    @2
    @3
    @1
    @4
    simpr
    eqcomd
    adantr
    cW
    @21
    @3
    cV
    swrdccatid
    syl3anc
    eqtrd
    3adant3
    @10
    @18
    @3
    c1
    caddc
    co
    #
    @13
    cfv
    #
    cY
    @10
    @17
    @30
    @13
    @9
    @5
    @17
    @30
    wceq
    @8
    @9
    @17
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @30
    c1
    @32
    cN
    cmin
    1e2m1
    oveq2i
    @9
    cN
    c2
    c1
    c3
    cN
    eluzelcn
    @9
    2cnd
    @9
    1cnd
    subsubd
    syl5eq
    3ad2ant3
    fveq2d
    @5
    @8
    @31
    cY
    wceq
    @9
    @3
    cV
    cW
    cX
    cY
    ccatw2s1p2
    3adant3
    eqtrd
    @5
    @8
    @19
    @9
    @3
    cV
    cW
    cX
    cY
    ccatw2s1p1
    3adant3
    3jca
end
