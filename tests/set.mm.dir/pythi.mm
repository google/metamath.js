include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ip2dii.mm"
include "id.mm"
include "cnv.mm"
include "wcel.mm"
include "wb.mm"
include "phnvi.mm"
include "diporthcom.mm"
include "mp3an.mm"
include "biimpi.mm"
include "oveq12d.mm"
include "00id.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cc.mm"
include "dipcl.mm"
include "addcli.mm"
include "addid1i.mm"
include "syl5eq.mm"
include "nvgcl.mm"
include "ipidsq.mm"
include "mp2an.mm"
include "oveq12i.mm"
include "3eqtr3g.mm"

theorem pythi
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  assume pyth.1: |- X = ( BaseSet ` U )
  assume pyth.2: |- G = ( +v ` U )
  assume pyth.6: |- N = ( normCV ` U )
  assume pyth.7: |- P = ( .iOLD ` U )
  assume pythi.u: |- U e. CPreHilOLD
  assume pythi.a: |- A e. X
  assume pythi.b: |- B e. X


  assert |- ( ( A P B ) = 0 -> ( ( N ` ( A G B ) ) ^ 2 ) = ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) )

  proof
    cA
    cB
    cP
    co
    #
    cc0
    wceq
    #
    cA
    cB
    cG
    co
    #
    @2
    cP
    co
    #
    cA
    cA
    cP
    co
    #
    cB
    cB
    cP
    co
    #
    caddc
    co
    #
    @2
    cN
    cfv
    c2
    cexp
    co
    #
    cA
    cN
    cfv
    c2
    cexp
    co
    #
    cB
    cN
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    @1
    @3
    @6
    @0
    cB
    cA
    cP
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @6
    cA
    cB
    cA
    cB
    cP
    cU
    cG
    cX
    pyth.1
    pyth.2
    pyth.7
    pythi.u
    pythi.a
    pythi.b
    pythi.a
    pythi.b
    ip2dii
    @1
    @12
    @6
    cc0
    caddc
    co
    @6
    @1
    @11
    cc0
    @6
    caddc
    @1
    @11
    cc0
    cc0
    caddc
    co
    cc0
    @1
    @0
    cc0
    @10
    cc0
    caddc
    @1
    id
    @1
    @10
    cc0
    wceq
    #
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @1
    @13
    wb
    cU
    pythi.u
    phnvi
    #
    pythi.a
    pythi.b
    cA
    cB
    cP
    cU
    cX
    pyth.1
    pyth.7
    diporthcom
    mp3an
    biimpi
    oveq12d
    00id
    syl6eq
    oveq2d
    @6
    @4
    @5
    @14
    @15
    @15
    @4
    cc
    wcel
    @17
    pythi.a
    pythi.a
    cA
    cA
    cP
    cU
    cX
    pyth.1
    pyth.7
    dipcl
    mp3an
    @14
    @16
    @16
    @5
    cc
    wcel
    @17
    pythi.b
    pythi.b
    cB
    cB
    cP
    cU
    cX
    pyth.1
    pyth.7
    dipcl
    mp3an
    addcli
    addid1i
    syl6eq
    syl5eq
    @14
    @2
    cX
    wcel
    #
    @3
    @7
    wceq
    @17
    @14
    @15
    @16
    @18
    @17
    pythi.a
    pythi.b
    cA
    cB
    cU
    cG
    cX
    pyth.1
    pyth.2
    nvgcl
    mp3an
    @2
    cP
    cU
    cN
    cX
    pyth.1
    pyth.6
    pyth.7
    ipidsq
    mp2an
    @4
    @8
    @5
    @9
    caddc
    @14
    @15
    @4
    @8
    wceq
    @17
    pythi.a
    cA
    cP
    cU
    cN
    cX
    pyth.1
    pyth.6
    pyth.7
    ipidsq
    mp2an
    @14
    @16
    @5
    @9
    wceq
    @17
    pythi.b
    cB
    cP
    cU
    cN
    cX
    pyth.1
    pyth.6
    pyth.7
    ipidsq
    mp2an
    oveq12i
    3eqtr3g
end
