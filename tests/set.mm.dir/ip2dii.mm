include "co.mm"
include "caddc.mm"
include "ccphlo.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "3pm3.2i.mm"
include "dipdi.mm"
include "mp2an.mm"
include "oveq12i.mm"
include "cnv.mm"
include "phnvi.mm"
include "nvgcl.mm"
include "mp3an.mm"
include "dipdir.mm"
include "cc.mm"
include "dipcl.mm"
include "add42i.mm"
include "3eqtr4i.mm"

theorem ip2dii
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cU: class U
  let cG: class G
  let cX: class X
  assume ip2dii.1: |- X = ( BaseSet ` U )
  assume ip2dii.2: |- G = ( +v ` U )
  assume ip2dii.7: |- P = ( .iOLD ` U )
  assume ip2dii.u: |- U e. CPreHilOLD
  assume ip2dii.a: |- A e. X
  assume ip2dii.b: |- B e. X
  assume ip2dii.c: |- C e. X
  assume ip2dii.d: |- D e. X


  assert |- ( ( A G B ) P ( C G D ) ) = ( ( ( A P C ) + ( B P D ) ) + ( ( A P D ) + ( B P C ) ) )

  proof
    cA
    cC
    cD
    cG
    co
    #
    cP
    co
    #
    cB
    @0
    cP
    co
    #
    caddc
    co
    #
    cA
    cC
    cP
    co
    #
    cA
    cD
    cP
    co
    #
    caddc
    co
    #
    cB
    cC
    cP
    co
    #
    cB
    cD
    cP
    co
    #
    caddc
    co
    #
    caddc
    co
    cA
    cB
    cG
    co
    @0
    cP
    co
    #
    @4
    @8
    caddc
    co
    @5
    @7
    caddc
    co
    caddc
    co
    @1
    @6
    @2
    @9
    caddc
    cU
    ccphlo
    wcel
    #
    cA
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    cD
    cX
    wcel
    #
    w3a
    @1
    @6
    wceq
    ip2dii.u
    @12
    @13
    @14
    ip2dii.a
    ip2dii.c
    ip2dii.d
    3pm3.2i
    cA
    cC
    cD
    cP
    cU
    cG
    cX
    ip2dii.1
    ip2dii.2
    ip2dii.7
    dipdi
    mp2an
    @11
    cB
    cX
    wcel
    #
    @13
    @14
    w3a
    @2
    @9
    wceq
    ip2dii.u
    @15
    @13
    @14
    ip2dii.b
    ip2dii.c
    ip2dii.d
    3pm3.2i
    cB
    cC
    cD
    cP
    cU
    cG
    cX
    ip2dii.1
    ip2dii.2
    ip2dii.7
    dipdi
    mp2an
    oveq12i
    @11
    @12
    @15
    @0
    cX
    wcel
    #
    w3a
    @10
    @3
    wceq
    ip2dii.u
    @12
    @15
    @16
    ip2dii.a
    ip2dii.b
    cU
    cnv
    wcel
    #
    @13
    @14
    @16
    cU
    ip2dii.u
    phnvi
    #
    ip2dii.c
    ip2dii.d
    cC
    cD
    cU
    cG
    cX
    ip2dii.1
    ip2dii.2
    nvgcl
    mp3an
    3pm3.2i
    cA
    cB
    @0
    cP
    cU
    cG
    cX
    ip2dii.1
    ip2dii.2
    ip2dii.7
    dipdir
    mp2an
    @4
    @8
    @5
    @7
    @17
    @12
    @13
    @4
    cc
    wcel
    @18
    ip2dii.a
    ip2dii.c
    cA
    cC
    cP
    cU
    cX
    ip2dii.1
    ip2dii.7
    dipcl
    mp3an
    @17
    @15
    @14
    @8
    cc
    wcel
    @18
    ip2dii.b
    ip2dii.d
    cB
    cD
    cP
    cU
    cX
    ip2dii.1
    ip2dii.7
    dipcl
    mp3an
    @17
    @12
    @14
    @5
    cc
    wcel
    @18
    ip2dii.a
    ip2dii.d
    cA
    cD
    cP
    cU
    cX
    ip2dii.1
    ip2dii.7
    dipcl
    mp3an
    @17
    @15
    @13
    @7
    cc
    wcel
    @18
    ip2dii.b
    ip2dii.c
    cB
    cC
    cP
    cU
    cX
    ip2dii.1
    ip2dii.7
    dipcl
    mp3an
    add42i
    3eqtr4i
end
