include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "ccht.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cfz.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cicc.mm"
include "cr.mm"
include "wceq.mm"
include "eluzelre.mm"
include "chtval.mm"
include "syl.mm"
include "cfl.mm"
include "cz.mm"
include "eluzel2.mm"
include "2z.mm"
include "ifcl.mm"
include "sylancl.mm"
include "a1i.mm"
include "zred.mm"
include "2re.mm"
include "min2.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "ppisval2.mm"
include "syl2anc.mm"
include "eluzelz.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "sumeq1d.mm"
include "c0.mm"
include "clt.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "inindir.mm"
include "0in.mm"
include "3eqtr3g.mm"
include "cun.mm"
include "min1.mm"
include "id.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzsplit.mm"
include "indir.mm"
include "syl6eq.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "wa.mm"
include "cn.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "oveq12d.mm"
include "fzfi.mm"
include "mp2an.mm"
include "cc.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "fsumcl.mm"
include "ssun2.mm"
include "pncan2d.mm"

theorem chtdif
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vn: setvar n
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cS: class S
  let cB: class B
  let cP: class P

  disjoint M p
  disjoint N p
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K p
  disjoint M x
  disjoint S s
  disjoint S x
  disjoint B k
  disjoint B n
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( N e. ( ZZ>= ` M ) -> ( ( theta ` N ) - ( theta ` M ) ) = sum_ p e. ( ( ( M + 1 ) ... N ) i^i Prime ) ( log ` p ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    ccht
    cfv
    #
    cM
    ccht
    cfv
    #
    cmin
    co
    cM
    c2
    cle
    wbr
    #
    cM
    c2
    cif
    #
    cM
    cfz
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cprime
    cin
    #
    @8
    vp
    csu
    #
    caddc
    co
    #
    @9
    cmin
    co
    @13
    @0
    @1
    @14
    @2
    @9
    cmin
    @0
    @1
    cc0
    cN
    cicc
    co
    cprime
    cin
    #
    @8
    vp
    csu
    #
    @14
    @0
    cN
    cr
    wcel
    #
    @1
    @16
    wceq
    cM
    cN
    eluzelre
    #
    cN
    vp
    chtval
    syl
    @0
    @16
    @4
    cN
    cfz
    co
    #
    cprime
    cin
    #
    @8
    vp
    csu
    @14
    @0
    @15
    @20
    @8
    vp
    @0
    @15
    @4
    cN
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @20
    @0
    @17
    c2
    @4
    cuz
    cfv
    #
    wcel
    #
    @15
    @23
    wceq
    @18
    @0
    @4
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    @4
    c2
    cle
    wbr
    #
    @25
    @0
    cM
    cz
    wcel
    #
    @27
    @26
    cM
    cN
    eluzel2
    #
    2z
    @3
    cM
    c2
    cz
    ifcl
    sylancl
    #
    @27
    @0
    2z
    a1i
    @0
    cM
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @28
    @0
    cM
    @30
    zred
    #
    2re
    cM
    c2
    min2
    sylancl
    @4
    c2
    eluz2
    syl3anbrc
    #
    cN
    @4
    ppisval2
    syl2anc
    @0
    @22
    @19
    cprime
    @0
    @21
    cN
    @4
    cfz
    @0
    cN
    cz
    wcel
    @21
    cN
    wceq
    cM
    cN
    eluzelz
    cN
    flid
    syl
    oveq2d
    ineq1d
    eqtrd
    sumeq1d
    @0
    @6
    @12
    @8
    @20
    vp
    @0
    @5
    @11
    cin
    #
    cprime
    cin
    c0
    cprime
    cin
    @6
    @12
    cin
    c0
    @0
    @36
    c0
    cprime
    @0
    cM
    @10
    clt
    wbr
    @36
    c0
    wceq
    @0
    cM
    @34
    ltp1d
    @4
    cM
    @10
    cN
    fzdisj
    syl
    ineq1d
    @5
    @11
    cprime
    inindir
    cprime
    0in
    3eqtr3g
    @0
    @20
    @5
    @11
    cun
    #
    cprime
    cin
    @6
    @12
    cun
    #
    @0
    @19
    @37
    cprime
    @0
    cM
    @19
    wcel
    #
    @19
    @37
    wceq
    @0
    cM
    @24
    wcel
    #
    @0
    @39
    @0
    @26
    @29
    @4
    cM
    cle
    wbr
    #
    @40
    @31
    @30
    @0
    @32
    @33
    @41
    @34
    2re
    cM
    c2
    min1
    sylancl
    @4
    cM
    eluz2
    syl3anbrc
    @0
    id
    cM
    @4
    cN
    elfzuzb
    sylanbrc
    cM
    @4
    cN
    fzsplit
    syl
    ineq1d
    @5
    @11
    cprime
    indir
    syl6eq
    #
    @0
    @19
    cfn
    wcel
    @20
    @19
    wss
    @20
    cfn
    wcel
    @0
    @4
    cN
    fzfid
    @19
    cprime
    inss1
    @19
    @20
    ssfi
    sylancl
    @0
    @7
    @20
    wcel
    #
    wa
    #
    @8
    @44
    @7
    @44
    @7
    @44
    @7
    cprime
    wcel
    @7
    cn
    wcel
    @44
    @20
    cprime
    @7
    @19
    cprime
    inss2
    @0
    @43
    simpr
    sseldi
    @7
    prmnn
    syl
    nnrpd
    relogcld
    recnd
    #
    fsumsplit
    eqtrd
    eqtrd
    @0
    @2
    cc0
    cM
    cicc
    co
    cprime
    cin
    #
    @8
    vp
    csu
    #
    @9
    @0
    @32
    @2
    @47
    wceq
    @34
    cM
    vp
    chtval
    syl
    @0
    @46
    @6
    @8
    vp
    @0
    @46
    @4
    cM
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @6
    @0
    @32
    @25
    @46
    @50
    wceq
    @34
    @35
    cM
    @4
    ppisval2
    syl2anc
    @0
    @49
    @5
    cprime
    @0
    @48
    cM
    @4
    cfz
    @0
    @29
    @48
    cM
    wceq
    @30
    cM
    flid
    syl
    oveq2d
    ineq1d
    eqtrd
    sumeq1d
    eqtrd
    oveq12d
    @0
    @9
    @13
    @0
    @6
    @8
    vp
    @6
    cfn
    wcel
    #
    @0
    @5
    cfn
    wcel
    @6
    @5
    wss
    @51
    @4
    cM
    fzfi
    @5
    cprime
    inss1
    @5
    @6
    ssfi
    mp2an
    a1i
    @0
    @7
    @6
    wcel
    @43
    @8
    cc
    wcel
    #
    @0
    @6
    @20
    @7
    @0
    @38
    @6
    @20
    @6
    @12
    ssun1
    @42
    syl5sseqr
    sselda
    @45
    syldan
    fsumcl
    @0
    @12
    @8
    vp
    @12
    cfn
    wcel
    #
    @0
    @11
    cfn
    wcel
    @12
    @11
    wss
    @53
    @10
    cN
    fzfi
    @11
    cprime
    inss1
    @11
    @12
    ssfi
    mp2an
    a1i
    @0
    @7
    @12
    wcel
    @43
    @52
    @0
    @12
    @20
    @7
    @0
    @38
    @12
    @20
    @12
    @6
    ssun2
    @42
    syl5sseqr
    sselda
    @45
    syldan
    fsumcl
    pncan2d
    eqtrd
end
