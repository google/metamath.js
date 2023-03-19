include "cdp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdp2.mm"
include "wceq.mm"
include "caddc.mm"
include "deccl.mm"
include "eqid.mm"
include "cn0.mm"
include "nn0mulcli.mm"
include "eqeltrri.mm"
include "nn0addcli.mm"
include "decmul1.mm"
include "oveq1i.mm"
include "dfdec10.mm"
include "10nn0.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "addassi.mm"
include "3eqtr3ri.mm"
include "oveq2i.mm"
include "adddii.mm"
include "eqtr3i.mm"
include "3eqtr2ri.mm"
include "3eqtr2i.mm"
include "3eqtri.mm"
include "decmul1c.mm"
include "decmul2c.mm"
include "wcel.mm"
include "cr.mm"
include "nn0rei.mm"
include "dpcl.mm"
include "mp2an.mm"
include "recni.mm"
include "mul4i.mm"
include "dec0u.mm"
include "dpmul10.mm"
include "oveq12i.mm"
include "3eqtr3i.mm"
include "dpmul100.mm"
include "3eqtr4i.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "dp2cl.mm"
include "10nn.mm"
include "decnncl2.mm"
include "nncni.mm"
include "nnne0i.mm"
include "pm3.2i.mm"
include "mulcan2.mm"
include "mp3an.mm"
include "mpbi.mm"

theorem dpmul
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  assume dpmul.a: |- A e. NN0
  assume dpmul.b: |- B e. NN0
  assume dpmul.c: |- C e. NN0
  assume dpmul.d: |- D e. NN0
  assume dpmul.e: |- E e. NN0
  assume dpmul.g: |- G e. NN0
  assume dpmul.j: |- J e. NN0
  assume dpmul.k: |- K e. NN0
  assume dpmul.1: |- ( A x. C ) = F
  assume dpmul.2: |- ( A x. D ) = M
  assume dpmul.3: |- ( B x. C ) = L
  assume dpmul.4: |- ( B x. D ) = ; E K
  assume dpmul.5: |- ( ( L + M ) + E ) = ; G J
  assume dpmul.6: |- ( F + G ) = I


  assert |- ( ( A . B ) x. ( C . D ) ) = ( I . _ J K )

  proof
    cA
    cB
    cdp
    co
    #
    cC
    cD
    cdp
    co
    #
    cmul
    co
    #
    c1
    cc0
    cdc
    #
    cc0
    cdc
    #
    cmul
    co
    #
    cI
    cJ
    cK
    cdp2
    #
    cdp
    co
    #
    @4
    cmul
    co
    #
    wceq
    #
    @2
    @7
    wceq
    #
    cA
    cB
    cdc
    #
    cC
    cD
    cdc
    #
    cmul
    co
    #
    cI
    cJ
    cdc
    #
    cK
    cdc
    @5
    @8
    cC
    cD
    @14
    cK
    @11
    cM
    cE
    caddc
    co
    #
    @12
    cA
    cB
    dpmul.a
    dpmul.b
    deccl
    dpmul.c
    dpmul.d
    @12
    eqid
    dpmul.k
    cM
    cE
    cA
    cD
    cmul
    co
    #
    cM
    cn0
    dpmul.2
    cA
    cD
    dpmul.a
    dpmul.d
    nn0mulcli
    eqeltrri
    #
    dpmul.e
    nn0addcli
    #
    @11
    cC
    cmul
    co
    #
    @15
    caddc
    co
    cF
    cL
    cdc
    #
    @15
    caddc
    co
    @3
    cF
    cmul
    co
    #
    cL
    caddc
    co
    #
    @15
    caddc
    co
    #
    @14
    @19
    @20
    @15
    caddc
    cA
    cB
    cF
    cL
    cC
    @11
    dpmul.c
    dpmul.a
    dpmul.b
    @11
    eqid
    #
    cB
    cC
    cmul
    co
    cL
    cn0
    dpmul.3
    cB
    cC
    dpmul.b
    dpmul.c
    nn0mulcli
    eqeltrri
    #
    dpmul.1
    dpmul.3
    decmul1
    oveq1i
    @20
    @22
    @15
    caddc
    cF
    cL
    dfdec10
    oveq1i
    @23
    @21
    cL
    @15
    caddc
    co
    #
    caddc
    co
    @21
    @3
    cG
    cmul
    co
    #
    cJ
    caddc
    co
    #
    caddc
    co
    #
    @14
    @21
    cL
    @15
    @3
    cF
    @3
    10nn0
    nn0cni
    #
    cF
    cA
    cC
    cmul
    co
    cF
    cn0
    dpmul.1
    cA
    cC
    dpmul.a
    dpmul.c
    nn0mulcli
    eqeltrri
    #
    nn0cni
    #
    mulcli
    #
    cL
    @25
    nn0cni
    #
    @15
    @18
    nn0cni
    addassi
    @28
    @26
    @21
    caddc
    cL
    cM
    caddc
    co
    cE
    caddc
    co
    cG
    cJ
    cdc
    @26
    @28
    dpmul.5
    cL
    cM
    cE
    @34
    cM
    @17
    nn0cni
    cE
    dpmul.e
    nn0cni
    addassi
    cG
    cJ
    dfdec10
    3eqtr3ri
    oveq2i
    @14
    @3
    cI
    cmul
    co
    #
    cJ
    caddc
    co
    @21
    @27
    caddc
    co
    #
    cJ
    caddc
    co
    @29
    cI
    cJ
    dfdec10
    @36
    @35
    cJ
    caddc
    @3
    cF
    cG
    caddc
    co
    #
    cmul
    co
    @36
    @35
    @3
    cF
    cG
    @30
    @32
    cG
    dpmul.g
    nn0cni
    #
    adddii
    @37
    cI
    @3
    cmul
    dpmul.6
    oveq2i
    eqtr3i
    oveq1i
    @21
    @27
    cJ
    @33
    @3
    cG
    @30
    @38
    mulcli
    cJ
    dpmul.j
    nn0cni
    addassi
    3eqtr2ri
    3eqtr2i
    3eqtri
    cA
    cB
    @15
    cK
    cD
    cE
    @11
    dpmul.d
    dpmul.a
    dpmul.b
    @24
    dpmul.k
    dpmul.e
    @16
    cM
    cE
    caddc
    dpmul.2
    oveq1i
    dpmul.4
    decmul1c
    decmul2c
    @2
    @3
    @3
    cmul
    co
    #
    cmul
    co
    @0
    @3
    cmul
    co
    #
    @1
    @3
    cmul
    co
    #
    cmul
    co
    @5
    @13
    @0
    @1
    @3
    @3
    @0
    cA
    cn0
    wcel
    cB
    cr
    wcel
    @0
    cr
    wcel
    dpmul.a
    cB
    dpmul.b
    nn0rei
    #
    cA
    cB
    dpcl
    mp2an
    recni
    #
    @1
    cC
    cn0
    wcel
    cD
    cr
    wcel
    @1
    cr
    wcel
    dpmul.c
    cD
    dpmul.d
    nn0rei
    #
    cC
    cD
    dpcl
    mp2an
    recni
    #
    @30
    @30
    mul4i
    @39
    @4
    @2
    cmul
    @3
    10nn0
    dec0u
    oveq2i
    @40
    @11
    @41
    @12
    cmul
    cA
    cB
    dpmul.a
    @42
    dpmul10
    cC
    cD
    dpmul.c
    @44
    dpmul10
    oveq12i
    3eqtr3i
    cI
    cJ
    cK
    @37
    cI
    cn0
    dpmul.6
    cF
    cG
    @31
    dpmul.g
    nn0addcli
    eqeltrri
    #
    dpmul.j
    cK
    dpmul.k
    nn0rei
    #
    dpmul100
    3eqtr4i
    @2
    cc
    wcel
    @7
    cc
    wcel
    @4
    cc
    wcel
    #
    @4
    cc0
    wne
    #
    wa
    @9
    @10
    wb
    @0
    @1
    @43
    @45
    mulcli
    @7
    cI
    cn0
    wcel
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    @46
    cJ
    cr
    wcel
    cK
    cr
    wcel
    @50
    cJ
    dpmul.j
    nn0rei
    @47
    cJ
    cK
    dp2cl
    mp2an
    cI
    @6
    dpcl
    mp2an
    recni
    @48
    @49
    @4
    @3
    10nn
    decnncl2
    #
    nncni
    @4
    @51
    nnne0i
    pm3.2i
    @2
    @7
    @4
    mulcan2
    mp3an
    mpbi
end
