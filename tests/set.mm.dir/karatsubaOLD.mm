include "c10.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "nn0cni.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "10nn0OLD.mm"
include "expcl.mm"
include "mp2an.mm"
include "mulcli.mm"
include "muladdi.mm"
include "addcli.mm"
include "add32i.mm"
include "adddiri.mm"
include "mul32i.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "mulassi.mm"
include "wceq.mm"
include "mulcomli.mm"
include "oveq12i.mm"
include "3eqtr2i.mm"
include "addcani.mm"
include "mpbi.mm"
include "3eqtri.mm"
include "3eqtr3ri.mm"
include "3eqtr3i.mm"

theorem karatsubaOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume karatsubaOLD.a: |- A e. NN0
  assume karatsubaOLD.b: |- B e. NN0
  assume karatsubaOLD.c: |- C e. NN0
  assume karatsubaOLD.d: |- D e. NN0
  assume karatsubaOLD.s: |- S e. NN0
  assume karatsubaOLD.m: |- M e. NN0
  assume karatsubaOLD.r: |- ( A x. C ) = R
  assume karatsubaOLD.t: |- ( B x. D ) = T
  assume karatsubaOLD.e: |- ( ( A + B ) x. ( C + D ) ) = ( ( R + S ) + T )
  assume karatsubaOLD.x: |- ( ( A x. ( 10 ^ M ) ) + B ) = X
  assume karatsubaOLD.y: |- ( ( C x. ( 10 ^ M ) ) + D ) = Y
  assume karatsubaOLD.w: |- ( ( R x. ( 10 ^ M ) ) + S ) = W
  assume karatsubaOLD.z: |- ( ( W x. ( 10 ^ M ) ) + T ) = Z


  assert |- ( X x. Y ) = Z

  proof
    cA
    c10
    cM
    cexp
    co
    #
    cmul
    co
    #
    cB
    caddc
    co
    #
    cC
    @0
    cmul
    co
    #
    cD
    caddc
    co
    #
    cmul
    co
    #
    cW
    @0
    cmul
    co
    #
    cT
    caddc
    co
    #
    cX
    cY
    cmul
    co
    cZ
    @5
    @1
    @3
    cmul
    co
    #
    cD
    cB
    cmul
    co
    #
    caddc
    co
    @1
    cD
    cmul
    co
    #
    @3
    cB
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @8
    @12
    caddc
    co
    #
    @9
    caddc
    co
    @7
    @1
    cB
    @3
    cD
    cA
    @0
    cA
    karatsubaOLD.a
    nn0cni
    #
    c10
    cc
    wcel
    cM
    cn0
    wcel
    @0
    cc
    wcel
    c10
    10nn0OLD
    nn0cni
    karatsubaOLD.m
    c10
    cM
    expcl
    mp2an
    #
    mulcli
    #
    cB
    karatsubaOLD.b
    nn0cni
    #
    cC
    @0
    cC
    karatsubaOLD.c
    nn0cni
    #
    @15
    mulcli
    #
    cD
    karatsubaOLD.d
    nn0cni
    #
    muladdi
    @8
    @9
    @12
    @1
    @3
    @16
    @19
    mulcli
    cD
    cB
    @20
    @17
    mulcli
    #
    @10
    @11
    @1
    cD
    @16
    @20
    mulcli
    @3
    cB
    @19
    @17
    mulcli
    addcli
    add32i
    @13
    @6
    @9
    cT
    caddc
    @1
    cC
    cmul
    co
    #
    cS
    caddc
    co
    #
    @0
    cmul
    co
    @22
    @0
    cmul
    co
    #
    cS
    @0
    cmul
    co
    #
    caddc
    co
    @6
    @13
    @22
    cS
    @0
    @1
    cC
    @16
    @18
    mulcli
    cS
    karatsubaOLD.s
    nn0cni
    #
    @15
    adddiri
    @23
    cW
    @0
    cmul
    @23
    cR
    @0
    cmul
    co
    #
    cS
    caddc
    co
    cW
    @22
    @27
    cS
    caddc
    @22
    cA
    cC
    cmul
    co
    #
    @0
    cmul
    co
    @27
    cA
    @0
    cC
    @14
    @15
    @18
    mul32i
    @28
    cR
    @0
    cmul
    karatsubaOLD.r
    oveq1i
    eqtri
    oveq1i
    karatsubaOLD.w
    eqtri
    oveq1i
    @24
    @8
    @25
    @12
    caddc
    @1
    cC
    @0
    @16
    @18
    @15
    mulassi
    @25
    cA
    cD
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    caddc
    co
    #
    @0
    cmul
    co
    @29
    @0
    cmul
    co
    #
    @30
    @0
    cmul
    co
    #
    caddc
    co
    @12
    cS
    @31
    @0
    cmul
    @28
    @9
    caddc
    co
    #
    cS
    caddc
    co
    #
    @34
    @31
    caddc
    co
    #
    wceq
    cS
    @31
    wceq
    @35
    cR
    cS
    caddc
    co
    #
    cT
    caddc
    co
    #
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    cmul
    co
    @36
    @35
    @28
    cS
    caddc
    co
    #
    @9
    caddc
    co
    @38
    @28
    @9
    cS
    cA
    cC
    @14
    @18
    mulcli
    #
    @21
    @26
    add32i
    @39
    @37
    @9
    cT
    caddc
    @28
    cR
    cS
    caddc
    karatsubaOLD.r
    oveq1i
    cB
    cD
    cT
    @17
    @20
    karatsubaOLD.t
    mulcomli
    #
    oveq12i
    eqtri
    karatsubaOLD.e
    cA
    cB
    cC
    cD
    @14
    @17
    @18
    @20
    muladdi
    3eqtr2i
    @34
    cS
    @31
    @28
    @9
    @40
    @21
    addcli
    @26
    @29
    @30
    cA
    cD
    @14
    @20
    mulcli
    #
    cC
    cB
    @18
    @17
    mulcli
    #
    addcli
    addcani
    mpbi
    oveq1i
    @29
    @30
    @0
    @42
    @43
    @15
    adddiri
    @32
    @10
    @33
    @11
    caddc
    cA
    cD
    @0
    @14
    @20
    @15
    mul32i
    cC
    cB
    @0
    @18
    @17
    @15
    mul32i
    oveq12i
    3eqtri
    oveq12i
    3eqtr3ri
    @41
    oveq12i
    3eqtri
    @2
    cX
    @4
    cY
    cmul
    karatsubaOLD.x
    karatsubaOLD.y
    oveq12i
    karatsubaOLD.z
    3eqtr3i
end
