include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "wo.mm"
include "simplr2.mm"
include "simpr2.mm"
include "anim1i.mm"
include "simplr3.mm"
include "adantr.mm"
include "breq1.mm"
include "weq.mm"
include "opeq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "sylc.mm"
include "orcd.mm"
include "ralrimiva.mm"
include "crab.mm"
include "sseq2i.mm"
include "ssrab.mm"
include "bitri.mm"
include "sylanbrc.mm"

theorem axcontlem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  assume axcontlem3.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }

  disjoint A p
  disjoint A x
  disjoint p x
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint p y
  disjoint x y
  disjoint N p
  disjoint N x
  disjoint N y
  disjoint U p
  disjoint U x
  disjoint U y
  disjoint Z p
  disjoint Z x
  disjoint Z y
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ ( Z e. ( EE ` N ) /\ U e. A /\ Z =/= U ) ) -> B C_ D )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wss
    #
    cB
    @1
    wss
    #
    vx
    cv
    #
    cZ
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    w3a
    wa
    #
    cZ
    @1
    wcel
    #
    cU
    cA
    wcel
    #
    cZ
    cU
    wne
    #
    w3a
    #
    wa
    #
    @3
    cU
    cZ
    vp
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @15
    cZ
    cU
    cop
    cbtwn
    wbr
    #
    wo
    #
    vp
    cB
    wral
    #
    cB
    cD
    wss
    #
    @2
    @3
    @8
    @0
    @13
    simplr2
    @14
    @19
    vp
    cB
    @14
    @15
    cB
    wcel
    #
    wa
    #
    @17
    @18
    @23
    @11
    @22
    wa
    @8
    @17
    @14
    @11
    @22
    @9
    @10
    @11
    @12
    simpr2
    anim1i
    @14
    @8
    @22
    @2
    @3
    @8
    @0
    @13
    simplr3
    adantr
    @7
    @17
    cU
    @6
    cbtwn
    wbr
    vx
    vy
    cU
    @15
    cA
    cB
    @4
    cU
    @6
    cbtwn
    breq1
    vy
    vp
    weq
    @6
    @16
    cU
    cbtwn
    @5
    @15
    cZ
    opeq2
    breq2d
    rspc2v
    sylc
    orcd
    ralrimiva
    @21
    cB
    @19
    vp
    @1
    crab
    #
    wss
    @3
    @20
    wa
    cD
    @24
    cB
    axcontlem3.1
    sseq2i
    @19
    vp
    @1
    cB
    ssrab
    bitri
    sylanbrc
end
