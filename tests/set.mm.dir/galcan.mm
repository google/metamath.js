include "cga.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "cminusg.mm"
include "cfv.mm"
include "oveq2.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "simpl.mm"
include "gagrp.mm"
include "syl.mm"
include "simpr1.mm"
include "eqid.mm"
include "grplinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "grpinvcl.mm"
include "simpr2.mm"
include "gaass.mm"
include "syl13anc.mm"
include "gagrpid.mm"
include "3eqtr3d.mm"
include "simpr3.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem galcan
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  assume galcan.1: |- X = ( Base ` G )


  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ ( A e. X /\ B e. Y /\ C e. Y ) ) -> ( ( A .(+) B ) = ( A .(+) C ) <-> B = C ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cY
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    c.po
    co
    #
    cA
    cC
    c.po
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    @8
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    @6
    c.po
    co
    #
    @11
    @7
    c.po
    co
    #
    wceq
    @5
    @9
    @6
    @7
    @11
    c.po
    oveq2
    @5
    @12
    cB
    @13
    cC
    @5
    @11
    cA
    cG
    cplusg
    cfv
    #
    co
    #
    cB
    c.po
    co
    #
    cG
    c0g
    cfv
    #
    cB
    c.po
    co
    #
    @12
    cB
    @5
    @15
    @17
    cB
    c.po
    @5
    cG
    cgrp
    wcel
    #
    @1
    @15
    @17
    wceq
    @5
    @0
    @19
    @0
    @4
    simpl
    #
    c.po
    cG
    cY
    gagrp
    syl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cX
    @14
    cG
    @10
    cA
    @17
    galcan.1
    @14
    eqid
    #
    @17
    eqid
    #
    @10
    eqid
    #
    grplinv
    syl2anc
    #
    oveq1d
    @5
    @0
    @11
    cX
    wcel
    #
    @1
    @2
    @16
    @12
    wceq
    @20
    @5
    @19
    @1
    @27
    @21
    @22
    cX
    cG
    @10
    cA
    galcan.1
    @25
    grpinvcl
    syl2anc
    #
    @22
    @0
    @1
    @2
    @3
    simpr2
    #
    @11
    cA
    cB
    @14
    c.po
    cG
    cX
    cY
    galcan.1
    @23
    gaass
    syl13anc
    @5
    @0
    @2
    @18
    cB
    wceq
    @20
    @29
    cB
    c.po
    cG
    cY
    @17
    @24
    gagrpid
    syl2anc
    3eqtr3d
    @5
    @15
    cC
    c.po
    co
    #
    @17
    cC
    c.po
    co
    #
    @13
    cC
    @5
    @15
    @17
    cC
    c.po
    @26
    oveq1d
    @5
    @0
    @27
    @1
    @3
    @30
    @13
    wceq
    @20
    @28
    @22
    @0
    @1
    @2
    @3
    simpr3
    #
    @11
    cA
    cC
    @14
    c.po
    cG
    cX
    cY
    galcan.1
    @23
    gaass
    syl13anc
    @5
    @0
    @3
    @31
    cC
    wceq
    @20
    @32
    cC
    c.po
    cG
    cY
    @17
    @24
    gagrpid
    syl2anc
    3eqtr3d
    eqeq12d
    syl5ib
    cB
    cC
    cA
    c.po
    oveq2
    impbid1
end
