include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmo.mm"
include "cle.mm"
include "nnre.mm"
include "reflcl.mm"
include "remulcl.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wa.mm"
include "sylan.mm"
include "syl.mm"
include "nnmulcl.mm"
include "nnred.mm"
include "3adant2.mm"
include "cc0.mm"
include "wne.mm"
include "cc.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "mulne0.mm"
include "redivcld.mm"
include "remulcld.mm"
include "wbr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "flmulnn0.mm"
include "lesub1dd.mm"
include "crp.mm"
include "wceq.mm"
include "nnrpd.mm"
include "modval.mm"
include "syl2anc.mm"
include "fldiv.mm"
include "recnd.mm"
include "divcan5.mm"
include "syl3an.mm"
include "fveq2d.mm"
include "recn.mm"
include "3eqtr4rd.mm"
include "3comr.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3brtr4d.mm"

theorem modmulnn
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN /\ A e. RR /\ M e. NN ) -> ( ( N x. ( |_ ` A ) ) mod ( N x. M ) ) <_ ( ( |_ ` ( N x. A ) ) mod ( N x. M ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cr
    wcel
    #
    cM
    cn
    wcel
    #
    w3a
    #
    cN
    cA
    cfl
    cfv
    #
    cmul
    co
    #
    cN
    cM
    cmul
    co
    #
    @5
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cN
    cA
    cmul
    co
    #
    cfl
    cfv
    #
    @9
    cmin
    co
    #
    @5
    @6
    cmo
    co
    #
    @12
    @6
    cmo
    co
    #
    cle
    @3
    @5
    @12
    @9
    @0
    @1
    @5
    cr
    wcel
    #
    @2
    @0
    cN
    cr
    wcel
    #
    @4
    cr
    wcel
    @16
    @1
    cN
    nnre
    #
    cA
    reflcl
    #
    cN
    @4
    remulcl
    syl2an
    3adant3
    #
    @0
    @1
    @12
    cr
    wcel
    #
    @2
    @0
    @1
    wa
    @11
    cr
    wcel
    #
    @21
    @0
    @17
    @1
    @22
    @18
    cN
    cA
    remulcl
    sylan
    #
    @11
    reflcl
    syl
    3adant3
    #
    @3
    @6
    @8
    @0
    @2
    @6
    cr
    wcel
    @1
    @0
    @2
    wa
    #
    @6
    cN
    cM
    nnmulcl
    #
    nnred
    3adant2
    #
    @3
    @7
    cr
    wcel
    @8
    cr
    wcel
    @3
    @5
    @6
    @20
    @27
    @0
    @2
    @6
    cc0
    wne
    #
    @1
    @0
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    cM
    cc
    wcel
    #
    cM
    cc0
    wne
    #
    wa
    #
    @28
    @2
    @0
    @29
    @30
    cN
    nncn
    cN
    nnne0
    jca
    #
    @2
    @32
    @33
    cM
    nncn
    cM
    nnne0
    jca
    #
    cN
    cM
    mulne0
    syl2an
    3adant2
    redivcld
    @7
    reflcl
    syl
    remulcld
    @0
    @1
    @5
    @12
    cle
    wbr
    #
    @2
    @0
    cN
    cn0
    wcel
    @1
    @37
    cN
    nnnn0
    cA
    cN
    flmulnn0
    sylan
    3adant3
    lesub1dd
    @3
    @16
    @6
    crp
    wcel
    #
    @14
    @10
    wceq
    @20
    @0
    @2
    @38
    @1
    @25
    @6
    @26
    nnrpd
    3adant2
    #
    @5
    @6
    modval
    syl2anc
    @3
    @15
    @12
    @6
    @12
    @6
    cdiv
    co
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @13
    @3
    @21
    @38
    @15
    @42
    wceq
    @24
    @39
    @12
    @6
    modval
    syl2anc
    @3
    @41
    @9
    @12
    cmin
    @3
    @40
    @8
    @6
    cmul
    @3
    @40
    @11
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    @8
    @3
    @22
    @6
    cn
    wcel
    #
    @40
    @44
    wceq
    @0
    @1
    @22
    @2
    @23
    3adant3
    @0
    @2
    @45
    @1
    @26
    3adant2
    @11
    @6
    fldiv
    syl2anc
    @1
    @2
    @0
    @44
    @8
    wceq
    @1
    @2
    @0
    w3a
    #
    @4
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    cA
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    @8
    @44
    @1
    @2
    @48
    @50
    wceq
    @0
    cA
    cM
    fldiv
    3adant3
    @46
    @7
    @47
    cfl
    @1
    @4
    cc
    wcel
    @2
    @34
    @0
    @31
    @7
    @47
    wceq
    @1
    @4
    @19
    recnd
    @36
    @35
    @4
    cM
    cN
    divcan5
    syl3an
    fveq2d
    @46
    @43
    @49
    cfl
    @1
    cA
    cc
    wcel
    @2
    @34
    @0
    @31
    @43
    @49
    wceq
    cA
    recn
    @36
    @35
    cA
    cM
    cN
    divcan5
    syl3an
    fveq2d
    3eqtr4rd
    3comr
    eqtrd
    oveq2d
    oveq2d
    eqtrd
    3brtr4d
end
