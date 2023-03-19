include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "nn0cni.mm"
include "cc.mm"
include "mulcli.mm"
include "addassi.mm"
include "eqtri.mm"
include "addcli.mm"
include "eqeltrri.mm"
include "subdii.mm"
include "oveq1i.mm"
include "wceq.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "eqcomi.mm"
include "numma.mm"
include "wcel.mm"
include "npcan.mm"
include "mp2an.mm"
include "subcli.mm"
include "eqtr3i.mm"
include "3eqtr4i.mm"

theorem nummac
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume numma.1: |- T e. NN0
  assume numma.2: |- A e. NN0
  assume numma.3: |- B e. NN0
  assume numma.4: |- C e. NN0
  assume numma.5: |- D e. NN0
  assume numma.6: |- M = ( ( T x. A ) + B )
  assume numma.7: |- N = ( ( T x. C ) + D )
  assume nummac.8: |- P e. NN0
  assume nummac.9: |- F e. NN0
  assume nummac.10: |- G e. NN0
  assume nummac.11: |- ( ( A x. P ) + ( C + G ) ) = E
  assume nummac.12: |- ( ( B x. P ) + D ) = ( ( T x. G ) + F )


  assert |- ( ( M x. P ) + N ) = ( ( T x. E ) + F )

  proof
    cT
    cE
    cG
    cmin
    co
    #
    cmul
    co
    #
    cT
    cG
    cmul
    co
    #
    cF
    caddc
    co
    #
    caddc
    co
    cT
    cE
    cmul
    co
    #
    @2
    cmin
    co
    #
    @3
    caddc
    co
    #
    cM
    cP
    cmul
    co
    cN
    caddc
    co
    @4
    cF
    caddc
    co
    #
    @1
    @5
    @3
    caddc
    cT
    cE
    cG
    cT
    numma.1
    nn0cni
    #
    cA
    cP
    cmul
    co
    #
    cC
    caddc
    co
    #
    cG
    caddc
    co
    #
    cE
    cc
    @11
    @9
    cC
    cG
    caddc
    co
    caddc
    co
    cE
    @9
    cC
    cG
    cA
    cP
    cA
    numma.2
    nn0cni
    cP
    nummac.8
    nn0cni
    mulcli
    #
    cC
    numma.4
    nn0cni
    #
    cG
    nummac.10
    nn0cni
    #
    addassi
    nummac.11
    eqtri
    #
    @10
    cG
    @9
    cC
    @12
    @13
    addcli
    #
    @14
    addcli
    eqeltrri
    #
    @14
    subdii
    oveq1i
    cA
    cB
    cC
    cD
    cP
    cT
    @0
    @3
    cM
    cN
    numma.1
    numma.2
    numma.3
    numma.4
    numma.5
    numma.6
    numma.7
    nummac.8
    @0
    @10
    @0
    @10
    wceq
    @11
    cE
    wceq
    @15
    cE
    cG
    @10
    @17
    @14
    @16
    subadd2i
    mpbir
    eqcomi
    nummac.12
    numma
    @5
    @2
    caddc
    co
    #
    cF
    caddc
    co
    @7
    @6
    @18
    @4
    cF
    caddc
    @4
    cc
    wcel
    @2
    cc
    wcel
    @18
    @4
    wceq
    cT
    cE
    @8
    @17
    mulcli
    #
    cT
    cG
    @8
    @14
    mulcli
    #
    @4
    @2
    npcan
    mp2an
    oveq1i
    @5
    @2
    cF
    @4
    @2
    @19
    @20
    subcli
    @20
    cF
    nummac.9
    nn0cni
    addassi
    eqtr3i
    3eqtr4i
end
