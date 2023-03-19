include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cgcd.mm"
include "wceq.mm"
include "cc0.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "cc.mm"
include "nncn.mm"
include "zcn.mm"
include "absmul.mm"
include "syl2an.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simpll.mm"
include "nnzd.mm"
include "nnz.mm"
include "zmulcl.mm"
include "sylan.mm"
include "gcdabs2.mm"
include "syl2anc.mm"
include "nnabscl.mm"
include "gcdmultiple.mm"
include "sylan2.mm"
include "anassrs.mm"
include "3eqtr3d.mm"
include "mul01.mm"
include "syl.mm"
include "cn0.mm"
include "nn0gcdid0.mm"
include "pm2.61ne.mm"

theorem gcdmultiplez
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. ZZ ) -> ( M gcd ( M x. N ) ) = M )

  proof
    cM
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cM
    cN
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    cM
    cM
    cc0
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    cN
    cc0
    cN
    cc0
    wceq
    #
    @4
    @6
    cM
    @7
    @3
    @5
    cM
    cgcd
    cN
    cc0
    cM
    cmul
    oveq2
    oveq2d
    eqeq1d
    @2
    cN
    cc0
    wne
    #
    wa
    #
    cM
    @3
    cabs
    cfv
    #
    cgcd
    co
    #
    cM
    cM
    cN
    cabs
    cfv
    #
    cmul
    co
    #
    cgcd
    co
    #
    @4
    cM
    @2
    @11
    @14
    wceq
    @8
    @2
    @10
    @13
    cM
    cgcd
    @2
    @10
    cM
    cabs
    cfv
    #
    @12
    cmul
    co
    #
    @13
    @0
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    @10
    @16
    wceq
    @1
    cM
    nncn
    #
    cN
    zcn
    cM
    cN
    absmul
    syl2an
    @0
    @16
    @13
    wceq
    @1
    @0
    @15
    cM
    @12
    cmul
    @0
    cM
    cM
    nnre
    @0
    cM
    cM
    nnnn0
    #
    nn0ge0d
    absidd
    oveq1d
    adantr
    eqtrd
    oveq2d
    adantr
    @9
    cM
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @11
    @4
    wceq
    @9
    cM
    @0
    @1
    @8
    simpll
    nnzd
    @2
    @21
    @8
    @0
    @20
    @1
    @21
    cM
    nnz
    cM
    cN
    zmulcl
    sylan
    adantr
    @3
    cM
    gcdabs2
    syl2anc
    @0
    @1
    @8
    @14
    cM
    wceq
    #
    @1
    @8
    wa
    @0
    @12
    cn
    wcel
    @22
    cN
    nnabscl
    cM
    @12
    gcdmultiple
    sylan2
    anassrs
    3eqtr3d
    @2
    @6
    cM
    cc0
    cgcd
    co
    #
    cM
    @0
    @6
    @23
    wceq
    #
    @1
    @0
    @17
    @24
    @18
    @17
    @5
    cc0
    cM
    cgcd
    cM
    mul01
    oveq2d
    syl
    adantr
    @0
    @23
    cM
    wceq
    #
    @1
    @0
    cM
    cn0
    wcel
    @25
    @19
    cM
    nn0gcdid0
    syl
    adantr
    eqtrd
    pm2.61ne
end
