include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cmul.mm"
include "gcdmultiple.mm"
include "3adant2.mm"
include "oveq1d.mm"
include "cz.mm"
include "nnz.mm"
include "3ad2ant1.mm"
include "zmulcl.mm"
include "syl2an.mm"
include "3adant1.mm"
include "gcdass.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "mulgcdr.mm"
include "syl3an.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "cc.mm"
include "nncn.mm"
include "3ad2ant3.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"

theorem rpmulgcd
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( K e. NN /\ M e. NN /\ N e. NN ) /\ ( K gcd M ) = 1 ) -> ( K gcd ( M x. N ) ) = ( K gcd N ) )

  proof
    cK
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cK
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    cK
    cM
    cN
    cmul
    co
    #
    cgcd
    co
    #
    cK
    cK
    cN
    cmul
    co
    #
    @7
    cgcd
    co
    #
    cgcd
    co
    #
    cK
    cN
    cgcd
    co
    @3
    @8
    @11
    wceq
    @5
    @3
    cK
    @9
    cgcd
    co
    #
    @7
    cgcd
    co
    #
    @8
    @11
    @3
    @12
    cK
    @7
    cgcd
    @0
    @2
    @12
    cK
    wceq
    @1
    cK
    cN
    gcdmultiple
    3adant2
    oveq1d
    @3
    cK
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @13
    @11
    wceq
    @0
    @1
    @14
    @2
    cK
    nnz
    #
    3ad2ant1
    @0
    @2
    @15
    @1
    @0
    @14
    cN
    cz
    wcel
    #
    @15
    @2
    @17
    cN
    nnz
    #
    cK
    cN
    zmulcl
    syl2an
    3adant2
    @1
    @2
    @16
    @0
    @1
    cM
    cz
    wcel
    #
    @18
    @16
    @2
    cM
    nnz
    #
    @19
    cM
    cN
    zmulcl
    syl2an
    3adant1
    @7
    @9
    cK
    gcdass
    syl3anc
    eqtr3d
    adantr
    @6
    @10
    cN
    cK
    cgcd
    @6
    @10
    c1
    cN
    cmul
    co
    #
    cN
    @3
    @5
    @10
    @4
    cN
    cmul
    co
    #
    @22
    @0
    @14
    @1
    @20
    @2
    cN
    cn0
    wcel
    @10
    @23
    wceq
    @17
    @21
    cN
    nnnn0
    cK
    cM
    cN
    mulgcdr
    syl3an
    @4
    c1
    cN
    cmul
    oveq1
    sylan9eq
    @6
    cN
    @3
    cN
    cc
    wcel
    #
    @5
    @2
    @0
    @24
    @1
    cN
    nncn
    3ad2ant3
    adantr
    mulid2d
    eqtrd
    oveq2d
    eqtrd
end
