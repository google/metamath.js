include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "cmul.mm"
include "caddc.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "nncni.mm"
include "expadd.mm"
include "mp3an.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "wtru.mm"
include "cz.mm"
include "cn.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "nn0zi.mm"
include "crp.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "modmul12d.mm"
include "trud.mm"
include "zcn.mm"
include "mulcli.mm"
include "nn0cni.mm"
include "addcomi.mm"
include "eqtri.mm"
include "cr.mm"
include "nn0rei.mm"
include "modcyc.mm"

theorem modxai
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume modxai.1: |- N e. NN
  assume modxai.2: |- A e. NN
  assume modxai.3: |- B e. NN0
  assume modxai.4: |- D e. ZZ
  assume modxai.5: |- K e. NN0
  assume modxai.6: |- M e. NN0
  assume modxai.7: |- C e. NN0
  assume modxai.8: |- L e. NN0
  assume modxai.11: |- ( ( A ^ B ) mod N ) = ( K mod N )
  assume modxai.12: |- ( ( A ^ C ) mod N ) = ( L mod N )
  assume modxai.9: |- ( B + C ) = E
  assume modxai.10: |- ( ( D x. N ) + M ) = ( K x. L )


  assert |- ( ( A ^ E ) mod N ) = ( M mod N )

  proof
    cA
    cE
    cexp
    co
    #
    cN
    cmo
    co
    cA
    cB
    cexp
    co
    #
    cA
    cC
    cexp
    co
    #
    cmul
    co
    #
    cN
    cmo
    co
    #
    cM
    cN
    cmo
    co
    #
    @0
    @3
    cN
    cmo
    cA
    cB
    cC
    caddc
    co
    #
    cexp
    co
    #
    @0
    @3
    @6
    cE
    cA
    cexp
    modxai.9
    oveq2i
    cA
    cc
    wcel
    cB
    cn0
    wcel
    #
    cC
    cn0
    wcel
    #
    @7
    @3
    wceq
    cA
    modxai.2
    nncni
    modxai.3
    modxai.7
    cA
    cB
    cC
    expadd
    mp3an
    eqtr3i
    oveq1i
    @4
    cM
    cD
    cN
    cmul
    co
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    @5
    @4
    cK
    cL
    cmul
    co
    #
    cN
    cmo
    co
    #
    @12
    @4
    @14
    wceq
    wtru
    @1
    cK
    @2
    cL
    cN
    @1
    cz
    wcel
    wtru
    @1
    cA
    cn
    wcel
    #
    @8
    @1
    cn
    wcel
    modxai.2
    modxai.3
    cA
    cB
    nnexpcl
    mp2an
    nnzi
    a1i
    cK
    cz
    wcel
    wtru
    cK
    modxai.5
    nn0zi
    a1i
    @2
    cz
    wcel
    wtru
    @2
    @15
    @9
    @2
    cn
    wcel
    modxai.2
    modxai.7
    cA
    cC
    nnexpcl
    mp2an
    nnzi
    a1i
    cL
    cz
    wcel
    wtru
    cL
    modxai.8
    nn0zi
    a1i
    cN
    crp
    wcel
    #
    wtru
    cN
    cn
    wcel
    @16
    modxai.1
    cN
    nnrp
    ax-mp
    #
    a1i
    @1
    cN
    cmo
    co
    cK
    cN
    cmo
    co
    wceq
    wtru
    modxai.11
    a1i
    @2
    cN
    cmo
    co
    cL
    cN
    cmo
    co
    wceq
    wtru
    modxai.12
    a1i
    modmul12d
    trud
    @13
    @11
    cN
    cmo
    @10
    cM
    caddc
    co
    @13
    @11
    modxai.10
    @10
    cM
    cD
    cN
    cD
    cz
    wcel
    #
    cD
    cc
    wcel
    modxai.4
    cD
    zcn
    ax-mp
    cN
    modxai.1
    nncni
    mulcli
    cM
    modxai.6
    nn0cni
    addcomi
    eqtr3i
    oveq1i
    eqtri
    cM
    cr
    wcel
    @16
    @18
    @12
    @5
    wceq
    cM
    modxai.6
    nn0rei
    @17
    modxai.4
    cM
    cN
    cD
    modcyc
    mp3an
    eqtri
    eqtri
end
