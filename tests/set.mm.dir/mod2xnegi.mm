include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cn.mm"
include "cn0.mm"
include "wcel.mm"
include "nn0nnaddcl.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "cz.mm"
include "nnzi.mm"
include "zaddcl.mm"
include "nnnn0i.mm"
include "nn0addcli.mm"
include "nn0zi.mm"
include "zsubcl.mm"
include "cmul.mm"
include "nncni.mm"
include "cc.mm"
include "zcn.mm"
include "ax-mp.mm"
include "addcli.mm"
include "subdiri.mm"
include "oveq1i.mm"
include "mulcli.mm"
include "nn0cni.mm"
include "addsubi.mm"
include "oveq2i.mm"
include "adddii.mm"
include "oveq12i.mm"
include "adddiri.mm"
include "addassi.mm"
include "eqtr2i.mm"
include "mulcomi.mm"
include "eqtr3i.mm"
include "wceq.mm"
include "mulsub.mm"
include "mp4an.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "3eqtr2i.mm"
include "mod2xi.mm"

theorem mod2xnegi
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume mod2xnegi.1: |- A e. NN
  assume mod2xnegi.2: |- B e. NN0
  assume mod2xnegi.3: |- D e. ZZ
  assume mod2xnegi.4: |- K e. NN
  assume mod2xnegi.5: |- M e. NN0
  assume mod2xnegi.6: |- L e. NN0
  assume mod2xnegi.10: |- ( ( A ^ B ) mod N ) = ( L mod N )
  assume mod2xnegi.7: |- ( 2 x. B ) = E
  assume mod2xnegi.8: |- ( L + K ) = N
  assume mod2xnegi.9: |- ( ( D x. N ) + M ) = ( K x. K )


  assert |- ( ( A ^ E ) mod N ) = ( M mod N )

  proof
    cA
    cB
    cN
    cD
    caddc
    co
    #
    cK
    cK
    caddc
    co
    #
    cmin
    co
    #
    cE
    cL
    cM
    cN
    cL
    cK
    caddc
    co
    #
    cN
    cn
    mod2xnegi.8
    cL
    cn0
    wcel
    cK
    cn
    wcel
    @3
    cn
    wcel
    mod2xnegi.6
    mod2xnegi.4
    cL
    cK
    nn0nnaddcl
    mp2an
    eqeltrri
    #
    mod2xnegi.1
    mod2xnegi.2
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    @2
    cz
    wcel
    cN
    cz
    wcel
    cD
    cz
    wcel
    #
    @5
    cN
    @4
    nnzi
    mod2xnegi.3
    cN
    cD
    zaddcl
    mp2an
    @1
    cK
    cK
    cK
    mod2xnegi.4
    nnnn0i
    #
    @7
    nn0addcli
    nn0zi
    @0
    @1
    zsubcl
    mp2an
    mod2xnegi.6
    mod2xnegi.5
    mod2xnegi.10
    mod2xnegi.7
    @2
    cN
    cmul
    co
    #
    cM
    caddc
    co
    @0
    cN
    cmul
    co
    #
    @1
    cN
    cmul
    co
    #
    cmin
    co
    #
    cM
    caddc
    co
    @9
    cM
    caddc
    co
    #
    @10
    cmin
    co
    #
    cL
    cL
    cmul
    co
    #
    @8
    @11
    cM
    caddc
    @0
    @1
    cN
    cN
    cD
    cN
    @4
    nncni
    #
    @6
    cD
    cc
    wcel
    mod2xnegi.3
    cD
    zcn
    ax-mp
    #
    addcli
    #
    cK
    cK
    cK
    mod2xnegi.4
    nncni
    #
    @18
    addcli
    #
    @15
    subdiri
    oveq1i
    @9
    cM
    @10
    @0
    cN
    @17
    @15
    mulcli
    cM
    mod2xnegi.5
    nn0cni
    #
    @1
    cN
    @19
    @15
    mulcli
    addsubi
    cN
    cN
    cmul
    co
    #
    cK
    cK
    cmul
    co
    #
    caddc
    co
    #
    cN
    cK
    cmul
    co
    #
    @24
    caddc
    co
    #
    cmin
    co
    #
    @13
    @14
    @21
    cD
    cN
    cmul
    co
    #
    cM
    caddc
    co
    #
    caddc
    co
    #
    cN
    @1
    cmul
    co
    #
    cmin
    co
    @26
    @13
    @29
    @23
    @30
    @25
    cmin
    @28
    @22
    @21
    caddc
    mod2xnegi.9
    oveq2i
    cN
    cK
    cK
    @15
    @18
    @18
    adddii
    oveq12i
    @29
    @12
    @30
    @10
    cmin
    @12
    @21
    @27
    caddc
    co
    #
    cM
    caddc
    co
    @29
    @9
    @31
    cM
    caddc
    cN
    cD
    cN
    @15
    @16
    @15
    adddiri
    oveq1i
    @21
    @27
    cM
    cN
    cN
    @15
    @15
    mulcli
    cD
    cN
    @16
    @15
    mulcli
    @20
    addassi
    eqtr2i
    cN
    @1
    @15
    @19
    mulcomi
    oveq12i
    eqtr3i
    cN
    cK
    cmin
    co
    #
    @32
    cmul
    co
    #
    @26
    @14
    cN
    cc
    wcel
    #
    cK
    cc
    wcel
    #
    @34
    @35
    @33
    @26
    wceq
    @15
    @18
    @15
    @18
    cN
    cK
    cN
    cK
    mulsub
    mp4an
    @32
    cL
    @32
    cL
    cmul
    @32
    cL
    wceq
    @3
    cN
    wceq
    mod2xnegi.8
    cN
    cK
    cL
    @15
    @18
    cL
    mod2xnegi.6
    nn0cni
    subadd2i
    mpbir
    #
    @36
    oveq12i
    eqtr3i
    eqtr3i
    3eqtr2i
    mod2xi
end
