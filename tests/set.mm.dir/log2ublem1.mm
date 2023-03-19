include "c3.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "c5.mm"
include "cmul.mm"
include "cdiv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "3nn.mm"
include "7nn0.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "5nn.mm"
include "7nn.mm"
include "nnmulcli.mm"
include "nncni.mm"
include "nn0cni.mm"
include "nnne0i.mm"
include "divassi.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wa.mm"
include "wb.mm"
include "3nn0.mm"
include "nn0expcli.mm"
include "5nn0.mm"
include "nn0mulcli.mm"
include "nn0rei.mm"
include "nnrei.mm"
include "nngt0i.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an.mm"
include "mpbir.mm"
include "eqbrtrri.mm"
include "remulcli.mm"
include "nndivre.mm"
include "le2addi.mm"
include "oveq2i.mm"
include "recni.mm"
include "adddii.mm"
include "eqtr2i.mm"
include "3brtr3i.mm"

theorem log2ublem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  assume log2ublem1.1: |- ( ( ( 3 ^ 7 ) x. ( 5 x. 7 ) ) x. A ) <_ B
  assume log2ublem1.2: |- A e. RR
  assume log2ublem1.3: |- D e. NN0
  assume log2ublem1.4: |- E e. NN
  assume log2ublem1.5: |- B e. NN0
  assume log2ublem1.6: |- F e. NN0
  assume log2ublem1.7: |- C = ( A + ( D / E ) )
  assume log2ublem1.8: |- ( B + F ) = G
  assume log2ublem1.9: |- ( ( ( 3 ^ 7 ) x. ( 5 x. 7 ) ) x. D ) <_ ( E x. F )


  assert |- ( ( ( 3 ^ 7 ) x. ( 5 x. 7 ) ) x. C ) <_ G

  proof
    c3
    c7
    cexp
    co
    #
    c5
    c7
    cmul
    co
    #
    cmul
    co
    #
    cA
    cmul
    co
    #
    @2
    cD
    cE
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cB
    cF
    caddc
    co
    #
    @2
    cC
    cmul
    co
    #
    cG
    cle
    @3
    cB
    cle
    wbr
    @5
    cF
    cle
    wbr
    @6
    @7
    cle
    wbr
    log2ublem1.1
    @2
    cD
    cmul
    co
    #
    cE
    cdiv
    co
    #
    @5
    cF
    cle
    @2
    cD
    cE
    @2
    @0
    @1
    c3
    cn
    wcel
    c7
    cn0
    wcel
    @0
    cn
    wcel
    3nn
    7nn0
    c3
    c7
    nnexpcl
    mp2an
    c5
    c7
    5nn
    7nn
    nnmulcli
    nnmulcli
    #
    nncni
    #
    cD
    log2ublem1.3
    nn0cni
    cE
    log2ublem1.4
    nncni
    cE
    log2ublem1.4
    nnne0i
    divassi
    @10
    cF
    cle
    wbr
    #
    @9
    cE
    cF
    cmul
    co
    cle
    wbr
    #
    log2ublem1.9
    @9
    cr
    wcel
    cF
    cr
    wcel
    cE
    cr
    wcel
    #
    cc0
    cE
    clt
    wbr
    #
    wa
    @13
    @14
    wb
    @9
    @2
    cD
    @0
    @1
    c3
    c7
    3nn0
    7nn0
    nn0expcli
    c5
    c7
    5nn0
    7nn0
    nn0mulcli
    nn0mulcli
    log2ublem1.3
    nn0mulcli
    nn0rei
    cF
    log2ublem1.6
    nn0rei
    #
    @15
    @16
    cE
    log2ublem1.4
    nnrei
    cE
    log2ublem1.4
    nngt0i
    pm3.2i
    @9
    cF
    cE
    ledivmul
    mp3an
    mpbir
    eqbrtrri
    @3
    @5
    cB
    cF
    @2
    cA
    @2
    @11
    nnrei
    #
    log2ublem1.2
    remulcli
    @2
    @4
    @18
    cD
    cr
    wcel
    cE
    cn
    wcel
    @4
    cr
    wcel
    cD
    log2ublem1.3
    nn0rei
    log2ublem1.4
    cD
    cE
    nndivre
    mp2an
    #
    remulcli
    cB
    log2ublem1.5
    nn0rei
    @17
    le2addi
    mp2an
    @8
    @2
    cA
    @4
    caddc
    co
    #
    cmul
    co
    @6
    cC
    @20
    @2
    cmul
    log2ublem1.7
    oveq2i
    @2
    cA
    @4
    @12
    cA
    log2ublem1.2
    recni
    @4
    @19
    recni
    adddii
    eqtr2i
    log2ublem1.8
    3brtr3i
end
