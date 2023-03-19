include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cn0.mm"
include "simpll.mm"
include "nnnn0.mm"
include "adantl.mm"
include "simplr.mm"
include "eqid.mm"
include "submmulg.mm"
include "syl3anc.mm"
include "subm0.mm"
include "ad2antrr.mm"
include "eqeq12d.mm"
include "rabbidva.mm"
include "eqeq1.mm"
include "infeq1.mm"
include "ifbieq2d.mm"
include "syl.mm"
include "cbs.mm"
include "submss.mm"
include "sselda.mm"
include "odval.mm"
include "simpr.mm"
include "wss.mm"
include "adantr.mm"
include "ressbas2.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"

theorem submod
  let cA: class A
  let cP: class P
  let cG: class G
  let cH: class H
  let cO: class O
  let cY: class Y
  let vx: setvar x
  assume submod.h: |- H = ( G |`s Y )
  assume submod.o: |- O = ( od ` G )
  assume submod.p: |- P = ( od ` H )


  assert |- ( ( Y e. ( SubMnd ` G ) /\ A e. Y ) -> ( O ` A ) = ( P ` A ) )

  proof
    cY
    cG
    csubmnd
    cfv
    wcel
    #
    cA
    cY
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    cG
    cmg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    vx
    cn
    crab
    #
    c0
    wceq
    #
    cc0
    @8
    cr
    clt
    cinf
    #
    cif
    #
    @3
    cA
    cH
    cmg
    cfv
    #
    co
    #
    cH
    c0g
    cfv
    #
    wceq
    #
    vx
    cn
    crab
    #
    c0
    wceq
    #
    cc0
    @16
    cr
    clt
    cinf
    #
    cif
    #
    cA
    cO
    cfv
    #
    cA
    cP
    cfv
    #
    @2
    @8
    @16
    wceq
    #
    @11
    @19
    wceq
    @2
    @7
    @15
    vx
    cn
    @2
    @3
    cn
    wcel
    #
    wa
    #
    @5
    @13
    @6
    @14
    @24
    @0
    @3
    cn0
    wcel
    #
    @1
    @5
    @13
    wceq
    @0
    @1
    @23
    simpll
    @23
    @25
    @2
    @3
    nnnn0
    adantl
    @0
    @1
    @23
    simplr
    cY
    @4
    @12
    cG
    cH
    @3
    cA
    @4
    eqid
    #
    submod.h
    @12
    eqid
    #
    submmulg
    syl3anc
    @0
    @6
    @14
    wceq
    @1
    @23
    cY
    cH
    cG
    @6
    submod.h
    @6
    eqid
    #
    subm0
    ad2antrr
    eqeq12d
    rabbidva
    @22
    @9
    @17
    @10
    @18
    cc0
    @8
    @16
    c0
    eqeq1
    cr
    @8
    @16
    clt
    infeq1
    ifbieq2d
    syl
    @2
    cA
    cG
    cbs
    cfv
    #
    wcel
    @20
    @11
    wceq
    @0
    cY
    @29
    cA
    @29
    cY
    cG
    @29
    eqid
    #
    submss
    #
    sselda
    vx
    cA
    @4
    cG
    @8
    cO
    @29
    @6
    @30
    @26
    @28
    submod.o
    @8
    eqid
    odval
    syl
    @2
    cA
    cH
    cbs
    cfv
    #
    wcel
    @21
    @19
    wceq
    @2
    cA
    cY
    @32
    @0
    @1
    simpr
    @2
    cY
    @29
    wss
    #
    cY
    @32
    wceq
    @0
    @33
    @1
    @31
    adantr
    cY
    @29
    cH
    cG
    submod.h
    @30
    ressbas2
    syl
    eleqtrd
    vx
    cA
    @12
    cH
    @16
    cP
    @32
    @14
    @32
    eqid
    @27
    @14
    eqid
    submod.p
    @16
    eqid
    odval
    syl
    3eqtr4d
end
