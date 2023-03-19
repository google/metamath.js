include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "nn0cni.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "10nn0.mm"
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

theorem karatsuba
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
  assume karatsuba.a: |- A e. NN0
  assume karatsuba.b: |- B e. NN0
  assume karatsuba.c: |- C e. NN0
  assume karatsuba.d: |- D e. NN0
  assume karatsuba.s: |- S e. NN0
  assume karatsuba.m: |- M e. NN0
  assume karatsuba.r: |- ( A x. C ) = R
  assume karatsuba.t: |- ( B x. D ) = T
  assume karatsuba.e: |- ( ( A + B ) x. ( C + D ) ) = ( ( R + S ) + T )
  assume karatsuba.x: |- ( ( A x. ( ; 1 0 ^ M ) ) + B ) = X
  assume karatsuba.y: |- ( ( C x. ( ; 1 0 ^ M ) ) + D ) = Y
  assume karatsuba.w: |- ( ( R x. ( ; 1 0 ^ M ) ) + S ) = W
  assume karatsuba.z: |- ( ( W x. ( ; 1 0 ^ M ) ) + T ) = Z


  assert |- ( X x. Y ) = Z

  proof
    cA
    c1
    cc0
    cdc
    #
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
    @1
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
    @1
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
    @6
    @2
    @4
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
    @2
    cD
    cmul
    co
    #
    @4
    cB
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @9
    @13
    caddc
    co
    #
    @10
    caddc
    co
    @8
    @2
    cB
    @4
    cD
    cA
    @1
    cA
    karatsuba.a
    nn0cni
    #
    @0
    cc
    wcel
    cM
    cn0
    wcel
    @1
    cc
    wcel
    @0
    10nn0
    nn0cni
    karatsuba.m
    @0
    cM
    expcl
    mp2an
    #
    mulcli
    #
    cB
    karatsuba.b
    nn0cni
    #
    cC
    @1
    cC
    karatsuba.c
    nn0cni
    #
    @16
    mulcli
    #
    cD
    karatsuba.d
    nn0cni
    #
    muladdi
    @9
    @10
    @13
    @2
    @4
    @17
    @20
    mulcli
    cD
    cB
    @21
    @18
    mulcli
    #
    @11
    @12
    @2
    cD
    @17
    @21
    mulcli
    @4
    cB
    @20
    @18
    mulcli
    addcli
    add32i
    @14
    @7
    @10
    cT
    caddc
    @2
    cC
    cmul
    co
    #
    cS
    caddc
    co
    #
    @1
    cmul
    co
    @23
    @1
    cmul
    co
    #
    cS
    @1
    cmul
    co
    #
    caddc
    co
    @7
    @14
    @23
    cS
    @1
    @2
    cC
    @17
    @19
    mulcli
    cS
    karatsuba.s
    nn0cni
    #
    @16
    adddiri
    @24
    cW
    @1
    cmul
    @24
    cR
    @1
    cmul
    co
    #
    cS
    caddc
    co
    cW
    @23
    @28
    cS
    caddc
    @23
    cA
    cC
    cmul
    co
    #
    @1
    cmul
    co
    @28
    cA
    @1
    cC
    @15
    @16
    @19
    mul32i
    @29
    cR
    @1
    cmul
    karatsuba.r
    oveq1i
    eqtri
    oveq1i
    karatsuba.w
    eqtri
    oveq1i
    @25
    @9
    @26
    @13
    caddc
    @2
    cC
    @1
    @17
    @19
    @16
    mulassi
    @26
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
    @1
    cmul
    co
    @30
    @1
    cmul
    co
    #
    @31
    @1
    cmul
    co
    #
    caddc
    co
    @13
    cS
    @32
    @1
    cmul
    @29
    @10
    caddc
    co
    #
    cS
    caddc
    co
    #
    @35
    @32
    caddc
    co
    #
    wceq
    cS
    @32
    wceq
    @36
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
    @37
    @36
    @29
    cS
    caddc
    co
    #
    @10
    caddc
    co
    @39
    @29
    @10
    cS
    cA
    cC
    @15
    @19
    mulcli
    #
    @22
    @27
    add32i
    @40
    @38
    @10
    cT
    caddc
    @29
    cR
    cS
    caddc
    karatsuba.r
    oveq1i
    cB
    cD
    cT
    @18
    @21
    karatsuba.t
    mulcomli
    #
    oveq12i
    eqtri
    karatsuba.e
    cA
    cB
    cC
    cD
    @15
    @18
    @19
    @21
    muladdi
    3eqtr2i
    @35
    cS
    @32
    @29
    @10
    @41
    @22
    addcli
    @27
    @30
    @31
    cA
    cD
    @15
    @21
    mulcli
    #
    cC
    cB
    @19
    @18
    mulcli
    #
    addcli
    addcani
    mpbi
    oveq1i
    @30
    @31
    @1
    @43
    @44
    @16
    adddiri
    @33
    @11
    @34
    @12
    caddc
    cA
    cD
    @1
    @15
    @21
    @16
    mul32i
    cC
    cB
    @1
    @19
    @18
    @16
    mul32i
    oveq12i
    3eqtri
    oveq12i
    3eqtr3ri
    @42
    oveq12i
    3eqtri
    @3
    cX
    @5
    cY
    cmul
    karatsuba.x
    karatsuba.y
    oveq12i
    karatsuba.z
    3eqtr3i
end
