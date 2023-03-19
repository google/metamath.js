include "cpr.mm"
include "clindeps.mm"
include "wbr.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wne.mm"
include "wrex.mm"
include "w3a.mm"
include "cz.mm"
include "cmap.mm"
include "c2.mm"
include "cop.mm"
include "c3.mm"
include "cneg.mm"
include "wcel.mm"
include "eqid.mm"
include "zlmodzxzldeplem1.mm"
include "zlmodzxzldeplem2.mm"
include "zlmodzxzldeplem3.mm"
include "zlmodzxzldeplem4.mm"
include "3pm3.2i.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cvv.mm"
include "cbs.mm"
include "cpw.mm"
include "wb.mm"
include "zring.mm"
include "c1.mm"
include "cfrlm.mm"
include "ovex.mm"
include "eqeltri.mm"
include "c6.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzel.mm"
include "c4.mm"
include "2z.mm"
include "4z.mm"
include "prelpwi.mm"
include "clmod.mm"
include "csca.mm"
include "zlmodzxzlmod.mm"
include "simpri.mm"
include "zringbas.mm"
include "zring0.mm"
include "islindeps.mm"
include "mpbir.mm"

theorem zlmodzxzldep
  let cA: class A
  let cB: class B
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }


  assert |- { A , B } linDepS Z

  proof
    cA
    cB
    cpr
    #
    cZ
    clindeps
    wbr
    #
    vx
    cv
    #
    cc0
    cfsupp
    wbr
    #
    @2
    @0
    cZ
    clinc
    cfv
    #
    co
    #
    cZ
    c0g
    cfv
    #
    wceq
    #
    vy
    cv
    #
    @2
    cfv
    #
    cc0
    wne
    #
    vy
    @0
    wrex
    #
    w3a
    #
    vx
    cz
    @0
    cmap
    co
    #
    wrex
    #
    cA
    c2
    cop
    cB
    c3
    cneg
    cop
    cpr
    #
    @13
    wcel
    @15
    cc0
    cfsupp
    wbr
    #
    @15
    @0
    @4
    co
    #
    @6
    wceq
    #
    @8
    @15
    cfv
    #
    cc0
    wne
    #
    vy
    @0
    wrex
    #
    w3a
    #
    @14
    cA
    cB
    @15
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    @15
    eqid
    #
    zlmodzxzldeplem1
    @16
    @18
    @21
    cA
    cB
    @15
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    @23
    zlmodzxzldeplem2
    cA
    cB
    @15
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    @23
    zlmodzxzldeplem3
    vy
    cA
    cB
    @15
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    @23
    zlmodzxzldeplem4
    3pm3.2i
    @12
    @22
    vx
    @15
    @13
    @2
    @15
    wceq
    #
    @3
    @16
    @7
    @18
    @11
    @21
    @2
    @15
    cc0
    cfsupp
    breq1
    @24
    @5
    @17
    @6
    @2
    @15
    @0
    @4
    oveq1
    eqeq1d
    @24
    @10
    @20
    vy
    @0
    @24
    @9
    @19
    cc0
    @8
    @2
    @15
    fveq1
    neeq1d
    rexbidv
    3anbi123d
    rspcev
    mp2an
    cZ
    cvv
    wcel
    @0
    cZ
    cbs
    cfv
    #
    cpw
    wcel
    #
    @1
    @14
    wb
    cZ
    zring
    cc0
    c1
    cpr
    #
    cfrlm
    co
    cvv
    zlmodzxzldep.z
    zring
    @27
    cfrlm
    ovex
    eqeltri
    cA
    @25
    wcel
    cB
    @25
    wcel
    @26
    cA
    cc0
    c3
    cop
    c1
    c6
    cop
    cpr
    #
    @25
    zlmodzxzldep.a
    c3
    cz
    wcel
    c6
    cz
    wcel
    @28
    @25
    wcel
    3z
    c6
    6nn
    nnzi
    c3
    c6
    cZ
    zlmodzxzldep.z
    zlmodzxzel
    mp2an
    eqeltri
    cB
    cc0
    c2
    cop
    c1
    c4
    cop
    cpr
    #
    @25
    zlmodzxzldep.b
    c2
    cz
    wcel
    c4
    cz
    wcel
    @29
    @25
    wcel
    2z
    4z
    c2
    c4
    cZ
    zlmodzxzldep.z
    zlmodzxzel
    mp2an
    eqeltri
    cA
    cB
    @25
    prelpwi
    mp2an
    vy
    @25
    zring
    @0
    vx
    cz
    cZ
    cvv
    cc0
    @6
    @25
    eqid
    @6
    eqid
    cZ
    clmod
    wcel
    zring
    cZ
    csca
    cfv
    wceq
    cZ
    zlmodzxzldep.z
    zlmodzxzlmod
    simpri
    zringbas
    zring0
    islindeps
    mp2an
    mpbir
end
