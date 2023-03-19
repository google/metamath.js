include "cn0.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cin.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "csn.mm"
include "cfv.mm"
include "cif.mm"
include "c0.mm"
include "wn.mm"
include "wceq.mm"
include "fzonel.mm"
include "a1i.mm"
include "disjsn.mm"
include "sylibr.mm"
include "ineq2d.mm"
include "inindi.mm"
include "in0.mm"
include "3eqtr3g.mm"
include "cun.mm"
include "cuz.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "syl.mm"
include "indi.mm"
include "syl6eq.mm"
include "cfn.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cn.mm"
include "2nn.mm"
include "inss1.mm"
include "simpl.mm"
include "syl5ss.mm"
include "sselda.mm"
include "nnexpcld.mm"
include "nncnd.mm"
include "fsumsplit.mm"
include "cpw.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "bitsinv.mm"
include "snssi.mm"
include "adantl.mm"
include "sseqin2.mm"
include "sylib.mm"
include "sumeq1d.mm"
include "cc.mm"
include "simplr.mm"
include "oveq2.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "sum0.mm"
include "syl6req.mm"
include "ifeqda.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem bitsinvp1
  let cA: class A
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume bitsinv.k: |- K = `' ( bits |` NN0 )


  assert |- ( ( A C_ NN0 /\ N e. NN0 ) -> ( K ` ( A i^i ( 0 ..^ ( N + 1 ) ) ) ) = ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + if ( N e. A , ( 2 ^ N ) , 0 ) ) )

  proof
    cA
    cn0
    wss
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cc0
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    #
    c2
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cA
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    @7
    vk
    csu
    #
    cA
    cN
    csn
    #
    cin
    #
    @7
    vk
    csu
    #
    caddc
    co
    @5
    cK
    cfv
    #
    @10
    cK
    cfv
    #
    cN
    cA
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
    @2
    @10
    @13
    @7
    @5
    vk
    @2
    cA
    @9
    @12
    cin
    #
    cin
    cA
    c0
    cin
    @10
    @13
    cin
    c0
    @2
    @20
    c0
    cA
    @2
    cN
    @9
    wcel
    wn
    #
    @20
    c0
    wceq
    @21
    @2
    cc0
    cN
    fzonel
    a1i
    @9
    cN
    disjsn
    sylibr
    ineq2d
    cA
    @9
    @12
    inindi
    cA
    in0
    3eqtr3g
    @2
    @5
    cA
    @9
    @12
    cun
    #
    cin
    @10
    @13
    cun
    @2
    @4
    @22
    cA
    @2
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @4
    @22
    wceq
    @2
    cN
    cn0
    @23
    @0
    @1
    simpr
    nn0uz
    syl6eleq
    cc0
    cN
    fzosplitsn
    syl
    ineq2d
    cA
    @9
    @12
    indi
    syl6eq
    @2
    @4
    cfn
    wcel
    #
    @5
    @4
    wss
    @5
    cfn
    wcel
    #
    @24
    @2
    cc0
    @3
    fzofi
    a1i
    cA
    @4
    inss2
    @4
    @5
    ssfi
    sylancl
    #
    @2
    @6
    @5
    wcel
    wa
    #
    @7
    @27
    c2
    @6
    c2
    cn
    wcel
    #
    @27
    2nn
    a1i
    @2
    @5
    cn0
    @6
    @2
    @5
    cA
    cn0
    cA
    @4
    inss1
    @0
    @1
    simpl
    #
    syl5ss
    #
    sselda
    nnexpcld
    nncnd
    fsumsplit
    @2
    @5
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    @15
    @8
    wceq
    @2
    @5
    cn0
    wss
    @25
    @32
    @30
    @26
    @5
    cn0
    elfpw
    sylanbrc
    @5
    vk
    cK
    bitsinv.k
    bitsinv
    syl
    @2
    @16
    @11
    @19
    @14
    caddc
    @2
    @10
    @31
    wcel
    #
    @16
    @11
    wceq
    @2
    @10
    cn0
    wss
    @10
    cfn
    wcel
    #
    @33
    @2
    @10
    cA
    cn0
    cA
    @9
    inss1
    @29
    syl5ss
    @2
    @9
    cfn
    wcel
    #
    @10
    @9
    wss
    @34
    @35
    @2
    cc0
    cN
    fzofi
    a1i
    cA
    @9
    inss2
    @9
    @10
    ssfi
    sylancl
    @10
    cn0
    elfpw
    sylanbrc
    @10
    vk
    cK
    bitsinv.k
    bitsinv
    syl
    @2
    @17
    @18
    cc0
    @14
    @2
    @17
    wa
    #
    @14
    @12
    @7
    vk
    csu
    #
    @18
    @36
    @13
    @12
    @7
    vk
    @36
    @12
    cA
    wss
    #
    @13
    @12
    wceq
    @17
    @38
    @2
    cN
    cA
    snssi
    adantl
    @12
    cA
    sseqin2
    sylib
    sumeq1d
    @36
    @17
    @18
    cc
    wcel
    @37
    @18
    wceq
    @2
    @17
    simpr
    @36
    @18
    @36
    c2
    cN
    @28
    @36
    2nn
    a1i
    @0
    @1
    @17
    simplr
    nnexpcld
    nncnd
    @7
    @18
    vk
    cN
    cA
    @6
    cN
    c2
    cexp
    oveq2
    sumsn
    syl2anc
    eqtr2d
    @2
    @17
    wn
    #
    wa
    #
    @14
    c0
    @7
    vk
    csu
    cc0
    @40
    @13
    c0
    @7
    vk
    @40
    @39
    @13
    c0
    wceq
    @2
    @39
    simpr
    cA
    cN
    disjsn
    sylibr
    sumeq1d
    @7
    vk
    sum0
    syl6req
    ifeqda
    oveq12d
    3eqtr4d
end
