include "cc0.mm"
include "c2.mm"
include "c3.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "c4.mm"
include "cpr.mm"
include "caddc.mm"
include "3cn.mm"
include "2timesi.mm"
include "3p3e6.mm"
include "eqtri.mm"
include "3t2e6.mm"
include "oveq12i.mm"
include "6cn.mm"
include "subidi.mm"
include "opeq2i.mm"
include "2t6m3t4e0.mm"
include "preq12i.mm"
include "oveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "2z.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzscm.mm"
include "mp3an.mm"
include "4z.mm"
include "zmulcl.mm"
include "mp2an.mm"
include "zlmodzxzsub.mm"
include "mp4an.mm"
include "3eqtr4i.mm"

theorem zlmodzxzequa
  let cA: class A
  let cB: class B
  let c.xb: class .xb
  let c.mi: class .-
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzequa.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzequa.o: |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. }
  assume zlmodzxzequa.t: |- .xb = ( .s ` Z )
  assume zlmodzxzequa.m: |- .- = ( -g ` Z )
  assume zlmodzxzequa.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzequa.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }


  assert |- ( ( 2 .xb A ) .- ( 3 .xb B ) ) = .0.

  proof
    cc0
    c2
    c3
    cmul
    co
    #
    c3
    c2
    cmul
    co
    #
    cmin
    co
    #
    cop
    #
    c1
    c2
    c6
    cmul
    co
    #
    c3
    c4
    cmul
    co
    #
    cmin
    co
    #
    cop
    #
    cpr
    #
    cc0
    cc0
    cop
    #
    c1
    cc0
    cop
    #
    cpr
    c2
    cA
    c.xb
    co
    #
    c3
    cB
    c.xb
    co
    #
    c.mi
    co
    #
    c.0
    @3
    @9
    @7
    @10
    @2
    cc0
    cc0
    @2
    c6
    c6
    cmin
    co
    cc0
    @0
    c6
    @1
    c6
    cmin
    @0
    c3
    c3
    caddc
    co
    c6
    c3
    3cn
    2timesi
    3p3e6
    eqtri
    3t2e6
    oveq12i
    c6
    6cn
    subidi
    eqtri
    opeq2i
    @6
    cc0
    c1
    2t6m3t4e0
    opeq2i
    preq12i
    @13
    cc0
    @0
    cop
    c1
    @4
    cop
    cpr
    #
    cc0
    @1
    cop
    c1
    @5
    cop
    cpr
    #
    c.mi
    co
    #
    @8
    @11
    @14
    @12
    @15
    c.mi
    @11
    c2
    cc0
    c3
    cop
    c1
    c6
    cop
    cpr
    #
    c.xb
    co
    #
    @14
    cA
    @17
    c2
    c.xb
    zlmodzxzequa.a
    oveq2i
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    c6
    cz
    wcel
    #
    @18
    @14
    wceq
    2z
    3z
    c6
    6nn
    nnzi
    #
    c2
    c3
    c6
    c.xb
    cZ
    zlmodzxzequa.z
    zlmodzxzequa.t
    zlmodzxzscm
    mp3an
    eqtri
    @12
    c3
    cc0
    c2
    cop
    c1
    c4
    cop
    cpr
    #
    c.xb
    co
    #
    @15
    cB
    @23
    c3
    c.xb
    zlmodzxzequa.b
    oveq2i
    @20
    @19
    c4
    cz
    wcel
    #
    @24
    @15
    wceq
    3z
    2z
    4z
    c3
    c2
    c4
    c.xb
    cZ
    zlmodzxzequa.z
    zlmodzxzequa.t
    zlmodzxzscm
    mp3an
    eqtri
    oveq12i
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @16
    @8
    wceq
    @19
    @20
    @26
    2z
    3z
    c2
    c3
    zmulcl
    mp2an
    @20
    @19
    @27
    3z
    2z
    c3
    c2
    zmulcl
    mp2an
    @19
    @21
    @28
    2z
    @22
    c2
    c6
    zmulcl
    mp2an
    @20
    @25
    @29
    3z
    4z
    c3
    c4
    zmulcl
    mp2an
    @0
    @1
    @4
    @5
    c.mi
    cZ
    zlmodzxzequa.z
    zlmodzxzequa.m
    zlmodzxzsub
    mp4an
    eqtri
    zlmodzxzequa.o
    3eqtr4i
end
