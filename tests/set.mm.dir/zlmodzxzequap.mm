include "cc0.mm"
include "c2.mm"
include "c3.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "c4.mm"
include "cpr.mm"
include "3cn.mm"
include "2cn.mm"
include "mulneg1i.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "mulcli.mm"
include "wa.mm"
include "cmin.mm"
include "negsub.mm"
include "mulcomi.mm"
include "subidi.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "mp2an.mm"
include "opeq2i.mm"
include "4cn.mm"
include "6cn.mm"
include "negsubi.mm"
include "2t6m3t4e0.mm"
include "preq12i.mm"
include "cz.mm"
include "2z.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzscm.mm"
include "mp3an.mm"
include "znegcl.mm"
include "ax-mp.mm"
include "4z.mm"
include "oveq12i.mm"
include "zmulcl.mm"
include "zlmodzxzadd.mm"
include "mp4an.mm"
include "3eqtr4i.mm"

theorem zlmodzxzequap
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.xb: class .xb
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }
  assume zlmodzxzequap.o: |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. }
  assume zlmodzxzequap.m: |- .+ = ( +g ` Z )
  assume zlmodzxzequap.t: |- .xb = ( .s ` Z )


  assert |- ( ( 2 .xb A ) .+ ( -u 3 .xb B ) ) = .0.

  proof
    cc0
    c2
    c3
    cmul
    co
    #
    c3
    cneg
    #
    c2
    cmul
    co
    #
    caddc
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
    @1
    c4
    cmul
    co
    #
    caddc
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
    @1
    cB
    c.xb
    co
    #
    c.pl
    co
    #
    c.0
    @4
    @10
    @8
    @11
    @3
    cc0
    cc0
    @3
    @0
    c3
    c2
    cmul
    co
    #
    cneg
    #
    caddc
    co
    #
    cc0
    @2
    @16
    @0
    caddc
    c3
    c2
    3cn
    2cn
    mulneg1i
    oveq2i
    @0
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @17
    cc0
    wceq
    c2
    c3
    2cn
    3cn
    mulcli
    #
    c3
    c2
    3cn
    2cn
    mulcli
    @18
    @19
    wa
    @17
    @0
    @15
    cmin
    co
    #
    cc0
    @0
    @15
    negsub
    @21
    @0
    @0
    cmin
    co
    cc0
    @15
    @0
    @0
    cmin
    c3
    c2
    3cn
    2cn
    mulcomi
    oveq2i
    @0
    @20
    subidi
    eqtri
    syl6eq
    mp2an
    eqtri
    opeq2i
    @7
    cc0
    c1
    @7
    @5
    c3
    c4
    cmul
    co
    #
    cneg
    #
    caddc
    co
    #
    cc0
    @6
    @23
    @5
    caddc
    c3
    c4
    3cn
    4cn
    mulneg1i
    oveq2i
    @24
    @5
    @22
    cmin
    co
    cc0
    @5
    @22
    c2
    c6
    2cn
    6cn
    mulcli
    c3
    c4
    3cn
    4cn
    mulcli
    negsubi
    2t6m3t4e0
    eqtri
    eqtri
    opeq2i
    preq12i
    @14
    cc0
    @0
    cop
    c1
    @5
    cop
    cpr
    #
    cc0
    @2
    cop
    c1
    @6
    cop
    cpr
    #
    c.pl
    co
    #
    @9
    @12
    @25
    @13
    @26
    c.pl
    @12
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
    @25
    cA
    @28
    c2
    c.xb
    zlmodzxzldep.a
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
    @29
    @25
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
    zlmodzxzldep.z
    zlmodzxzequap.t
    zlmodzxzscm
    mp3an
    eqtri
    @13
    @1
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
    @26
    cB
    @34
    @1
    c.xb
    zlmodzxzldep.b
    oveq2i
    @1
    cz
    wcel
    #
    @30
    c4
    cz
    wcel
    #
    @35
    @26
    wceq
    @31
    @36
    3z
    c3
    znegcl
    ax-mp
    #
    2z
    4z
    @1
    c2
    c4
    c.xb
    cZ
    zlmodzxzldep.z
    zlmodzxzequap.t
    zlmodzxzscm
    mp3an
    eqtri
    oveq12i
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @27
    @9
    wceq
    @30
    @31
    @39
    2z
    3z
    c2
    c3
    zmulcl
    mp2an
    @36
    @30
    @40
    @38
    2z
    @1
    c2
    zmulcl
    mp2an
    @30
    @32
    @41
    2z
    @33
    c2
    c6
    zmulcl
    mp2an
    @36
    @37
    @42
    @38
    4z
    @1
    c4
    zmulcl
    mp2an
    @0
    @2
    @5
    @6
    c.pl
    cZ
    zlmodzxzldep.z
    zlmodzxzequap.m
    zlmodzxzadd
    mp4an
    eqtri
    zlmodzxzequap.o
    3eqtr4i
end
