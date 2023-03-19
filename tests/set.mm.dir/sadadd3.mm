include "csad.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cfv.mm"
include "c0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "cif.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "iddvds.mm"
include "syl.mm"
include "dvds0.mm"
include "breq2.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "inss1.mm"
include "cv.mm"
include "whad.mm"
include "crab.mm"
include "sadfval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "wf.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "wf1o.mm"
include "bitsf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "feq1i.mm"
include "mpbir.mm"
include "ffvelrni.mm"
include "nn0cnd.mm"
include "cc.mm"
include "nncnd.mm"
include "0cn.mm"
include "ifcl.mm"
include "pncan2d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "nn0zd.mm"
include "adantr.mm"
include "wn.mm"
include "wa.mm"
include "0zd.mm"
include "ifclda.mm"
include "zaddcld.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "sadadd2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem sadadd3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadcp1.n: |- ( ph -> N e. NN0 )
  assume sadcadd.k: |- K = `' ( bits |` NN0 )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint N n
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( K ` ( ( A sadd B ) i^i ( 0 ..^ N ) ) ) mod ( 2 ^ N ) ) = ( ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + ( K ` ( B i^i ( 0 ..^ N ) ) ) ) mod ( 2 ^ N ) ) )

  proof
    wph
    cA
    cB
    csad
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    c0
    cN
    cC
    cfv
    wcel
    #
    c2
    cN
    cexp
    co
    #
    cc0
    cif
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    @3
    @5
    cmo
    co
    #
    cA
    @1
    cin
    cK
    cfv
    cB
    @1
    cin
    cK
    cfv
    caddc
    co
    #
    @5
    cmo
    co
    wph
    @8
    @9
    wceq
    #
    @5
    @7
    @3
    cmin
    co
    #
    cdvds
    wbr
    #
    wph
    @5
    @6
    @12
    cdvds
    wph
    @5
    @5
    cdvds
    wbr
    #
    @5
    cc0
    cdvds
    wbr
    #
    @5
    @6
    cdvds
    wbr
    #
    wph
    @5
    cz
    wcel
    #
    @14
    wph
    @5
    wph
    c2
    cN
    c2
    cn
    wcel
    wph
    2nn
    a1i
    sadcp1.n
    nnexpcld
    #
    nnzd
    #
    @5
    iddvds
    syl
    wph
    @17
    @15
    @19
    @5
    dvds0
    syl
    @4
    @14
    @15
    @16
    @5
    cc0
    @5
    @6
    @5
    cdvds
    breq2
    cc0
    @6
    @5
    cdvds
    breq2
    ifboth
    syl2anc
    wph
    @3
    @6
    wph
    @3
    wph
    @2
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    @3
    cn0
    wcel
    wph
    @2
    cn0
    wss
    @2
    cfn
    wcel
    #
    @21
    wph
    @2
    @0
    cn0
    @0
    @1
    inss1
    wph
    @0
    vk
    cv
    #
    cA
    wcel
    @23
    cB
    wcel
    c0
    @23
    cC
    cfv
    wcel
    whad
    #
    vk
    cn0
    crab
    cn0
    wph
    cA
    cB
    cC
    vk
    vm
    vn
    vc
    sadval.a
    sadval.b
    sadval.c
    sadfval
    @24
    vk
    cn0
    ssrab2
    syl6eqss
    syl5ss
    wph
    @1
    cfn
    wcel
    #
    @2
    @1
    wss
    @22
    @25
    wph
    cc0
    cN
    fzofi
    a1i
    @0
    @1
    inss2
    @1
    @2
    ssfi
    sylancl
    @2
    cn0
    elfpw
    sylanbrc
    @20
    cn0
    @2
    cK
    @20
    cn0
    cK
    wf
    @20
    cn0
    cbits
    cn0
    cres
    #
    ccnv
    #
    wf
    #
    cn0
    @20
    @26
    wf1o
    @20
    cn0
    @27
    wf1o
    @28
    bitsf1o
    cn0
    @20
    @26
    f1ocnv
    @20
    cn0
    @27
    f1of
    mp2b
    @20
    cn0
    cK
    @27
    sadcadd.k
    feq1i
    mpbir
    ffvelrni
    syl
    #
    nn0cnd
    wph
    @5
    cc
    wcel
    cc0
    cc
    wcel
    @6
    cc
    wcel
    wph
    @5
    @18
    nncnd
    0cn
    @4
    @5
    cc0
    cc
    ifcl
    sylancl
    pncan2d
    breqtrrd
    wph
    @5
    cn
    wcel
    @7
    cz
    wcel
    @3
    cz
    wcel
    @11
    @13
    wb
    @18
    wph
    @3
    @6
    wph
    @3
    @29
    nn0zd
    #
    wph
    @4
    @5
    cc0
    cz
    wph
    @17
    @4
    @19
    adantr
    wph
    @4
    wn
    wa
    0zd
    ifclda
    zaddcld
    @30
    @7
    @3
    @5
    moddvds
    syl3anc
    mpbird
    wph
    @7
    @10
    @5
    cmo
    wph
    cA
    cB
    cC
    vm
    vn
    cK
    cN
    vc
    sadval.a
    sadval.b
    sadval.c
    sadcp1.n
    sadcadd.k
    sadadd2
    oveq1d
    eqtr3d
end
