include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "crmx.mm"
include "co.mm"
include "wceq.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "crmy.mm"
include "cmul.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "nn0sqcl.mm"
include "3ad2ant3.mm"
include "nn0cnd.mm"
include "cz.mm"
include "simp1.mm"
include "nn0z.mm"
include "3ad2ant2.mm"
include "frmx.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "syl.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nnnn0d.mm"
include "3ad2ant1.mm"
include "rmynn0.mm"
include "3adant3.mm"
include "nn0mulcld.mm"
include "subcan2ad.mm"
include "rmxynorm.mm"
include "eqeq2d.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "sq11.mm"
include "3bitr3rd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "ceqsrexv.mm"
include "bitr4d.mm"

theorem rmxdiophlem
  let vy: setvar y
  let cA: class A
  let cN: class N
  let cX: class X

  disjoint A y
  disjoint N y
  disjoint X y
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 /\ X e. NN0 ) -> ( X = ( A rmX N ) <-> E. y e. NN0 ( y = ( A rmY N ) /\ ( ( X ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( y ^ 2 ) ) ) = 1 ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cn0
    wcel
    #
    w3a
    #
    cX
    cA
    cN
    crmx
    co
    #
    wceq
    #
    cX
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cA
    cN
    crmy
    co
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    vy
    cv
    #
    @9
    wceq
    #
    @7
    @8
    @14
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    vy
    cn0
    wrex
    #
    @4
    @12
    @5
    c2
    cexp
    co
    #
    @11
    cmin
    co
    #
    wceq
    @7
    @21
    wceq
    #
    @13
    @6
    @4
    @7
    @21
    @11
    @4
    @7
    @3
    @1
    @7
    cn0
    wcel
    @2
    cX
    nn0sqcl
    3ad2ant3
    nn0cnd
    @4
    @21
    @4
    @5
    cn0
    wcel
    #
    @21
    cn0
    wcel
    @4
    @1
    cN
    cz
    wcel
    #
    @24
    @1
    @2
    @3
    simp1
    #
    @2
    @1
    @25
    @3
    cN
    nn0z
    3ad2ant2
    #
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    syl2anc
    #
    @5
    nn0sqcl
    syl
    nn0cnd
    @4
    @11
    @4
    @8
    @10
    @1
    @2
    @8
    cn0
    wcel
    @3
    @1
    @8
    @1
    @8
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    nnnn0d
    3ad2ant1
    @4
    @9
    cn0
    wcel
    #
    @10
    cn0
    wcel
    @1
    @2
    @29
    @3
    cA
    cN
    rmynn0
    3adant3
    #
    @9
    nn0sqcl
    syl
    nn0mulcld
    nn0cnd
    subcan2ad
    @4
    @22
    c1
    @12
    @4
    @1
    @25
    @22
    c1
    wceq
    @26
    @27
    cA
    cN
    rmxynorm
    syl2anc
    eqeq2d
    @4
    cX
    cr
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    wa
    #
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    @23
    @6
    wb
    @3
    @1
    @33
    @2
    @3
    @31
    @32
    cX
    nn0re
    cX
    nn0ge0
    jca
    3ad2ant3
    @4
    @24
    @36
    @28
    @24
    @34
    @35
    @5
    nn0re
    @5
    nn0ge0
    jca
    syl
    cX
    @5
    sq11
    syl2anc
    3bitr3rd
    @4
    @29
    @20
    @13
    wb
    @30
    @19
    @13
    vy
    @9
    cn0
    @15
    @18
    @12
    c1
    @15
    @17
    @11
    @7
    cmin
    @15
    @16
    @10
    @8
    cmul
    @14
    @9
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    ceqsrexv
    syl
    bitr4d
end
