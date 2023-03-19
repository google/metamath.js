include "cr.mm"
include "wcel.mm"
include "cchp.mm"
include "cfv.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cc0.mm"
include "cicc.mm"
include "cprime.mm"
include "cin.mm"
include "clog.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmul.mm"
include "chpval.mm"
include "fveq2.mm"
include "id.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "recnd.mm"
include "wceq.mm"
include "simprr.mm"
include "fsumvma2.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "vmappw.mm"
include "syl2an.mm"
include "sumeq2dv.mm"
include "chash.mm"
include "cfn.mm"
include "cc.mm"
include "fzfid.mm"
include "c2.mm"
include "cuz.mm"
include "crp.mm"
include "prmuz2.mm"
include "eluzelre.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "rplogcld.mm"
include "3syl.mm"
include "rpcnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cn0.mm"
include "cle.mm"
include "ppisval.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "elfzuz2.mm"
include "simpl.mm"
include "0red.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "eluzle.mm"
include "cz.mm"
include "wb.mm"
include "2z.mm"
include "flge.mm"
include "mpan2.mm"
include "syl5ibr.mm"
include "imp.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "syldan.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "1red.mm"
include "1lt2.mm"
include "rplogcl.mm"
include "rpdivcld.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem chpval2
  let cA: class A
  let vp: setvar p
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x

  disjoint A p
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d p
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A x
  assert |- ( A e. RR -> ( psi ` A ) = sum_ p e. ( ( 0 [,] A ) i^i Prime ) ( ( log ` p ) x. ( |_ ` ( ( log ` A ) / ( log ` p ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cchp
    cfv
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    c1
    cA
    clog
    cfv
    #
    vp
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @8
    vk
    cv
    #
    cexp
    co
    #
    cvma
    cfv
    #
    vk
    csu
    #
    vp
    csu
    @6
    @9
    @11
    cmul
    co
    #
    vp
    csu
    cA
    vn
    chpval
    @0
    vn
    cA
    @4
    @15
    vk
    vp
    @3
    @14
    cvma
    fveq2
    @0
    id
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @19
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @18
    @20
    @0
    @3
    @1
    elfznn
    adantl
    @3
    vmacl
    syl
    recnd
    @0
    @18
    @4
    cc0
    wceq
    simprr
    fsumvma2
    @0
    @6
    @16
    @17
    vp
    @0
    @8
    @6
    wcel
    #
    wa
    #
    @16
    @12
    @9
    vk
    csu
    #
    @17
    @22
    @12
    @15
    @9
    vk
    @22
    @8
    cprime
    wcel
    #
    @13
    cn
    wcel
    @15
    @9
    wceq
    @13
    @12
    wcel
    @22
    @6
    cprime
    @8
    @5
    cprime
    inss2
    @0
    @21
    simpr
    sseldi
    #
    @13
    @11
    elfznn
    @8
    @13
    vmappw
    syl2an
    sumeq2dv
    @22
    @23
    @12
    chash
    cfv
    #
    @9
    cmul
    co
    #
    @11
    @9
    cmul
    co
    @17
    @22
    @12
    cfn
    wcel
    @9
    cc
    wcel
    @23
    @27
    wceq
    @22
    c1
    @11
    fzfid
    @22
    @9
    @22
    @24
    @8
    c2
    cuz
    cfv
    #
    wcel
    #
    @9
    crp
    wcel
    @25
    @8
    prmuz2
    @29
    @8
    c2
    @8
    eluzelre
    @29
    @8
    cn
    wcel
    c1
    @8
    clt
    wbr
    @8
    eluz2b2
    simprbi
    rplogcld
    3syl
    #
    rpcnd
    #
    @12
    @9
    vk
    fsumconst
    syl2anc
    @22
    @26
    @11
    @9
    cmul
    @22
    @11
    cn0
    wcel
    #
    @26
    @11
    wceq
    @22
    @10
    cr
    wcel
    cc0
    @10
    cle
    wbr
    @32
    @22
    @7
    @9
    @22
    cA
    @0
    @21
    @1
    @28
    wcel
    #
    cA
    crp
    wcel
    @22
    @8
    c2
    @1
    cfz
    co
    #
    wcel
    @33
    @0
    @6
    @34
    @8
    @0
    @6
    @34
    cprime
    cin
    @34
    cA
    ppisval
    @34
    cprime
    inss1
    syl6eqss
    sselda
    @8
    c2
    @1
    elfzuz2
    syl
    #
    @0
    @33
    wa
    #
    cA
    @0
    @33
    simpl
    #
    @36
    cc0
    c2
    cA
    @36
    0red
    c2
    cr
    wcel
    @36
    2re
    a1i
    #
    @37
    cc0
    c2
    clt
    wbr
    @36
    2pos
    a1i
    @0
    @33
    c2
    cA
    cle
    wbr
    #
    @33
    @39
    @0
    c2
    @1
    cle
    wbr
    #
    c2
    @1
    eluzle
    @0
    c2
    cz
    wcel
    @39
    @40
    wb
    2z
    cA
    c2
    flge
    mpan2
    syl5ibr
    imp
    #
    ltletrd
    elrpd
    syldan
    relogcld
    @30
    rerpdivcld
    @22
    @10
    @22
    @7
    @9
    @0
    @21
    c1
    cA
    clt
    wbr
    #
    @7
    crp
    wcel
    @0
    @21
    @33
    @42
    @35
    @36
    c1
    c2
    cA
    @36
    1red
    @38
    @37
    c1
    c2
    clt
    wbr
    @36
    1lt2
    a1i
    @41
    ltletrd
    syldan
    cA
    rplogcl
    syldan
    @30
    rpdivcld
    rpge0d
    @10
    flge0nn0
    syl2anc
    #
    @11
    hashfz1
    syl
    oveq1d
    @22
    @11
    @9
    @22
    @11
    @43
    nn0cnd
    @31
    mulcomd
    3eqtrd
    eqtrd
    sumeq2dv
    3eqtrd
end
