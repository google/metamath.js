include "cga.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "gagrp.mm"
include "adantr.mm"
include "simpr1.mm"
include "eqid.mm"
include "grprinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simpl.mm"
include "grpinvcl.mm"
include "simpr3.mm"
include "gaass.mm"
include "syl13anc.mm"
include "gagrpid.mm"
include "3eqtr3d.mm"
include "eqeq2d.mm"
include "wb.mm"
include "simpr2.mm"
include "cxp.mm"
include "wf.mm"
include "gaf.mm"
include "fovrnd.mm"
include "galcan.mm"
include "bitr3d.mm"
include "eqcom.mm"
include "syl6bb.mm"

theorem gacan
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume galcan.1: |- X = ( Base ` G )
  assume gacan.2: |- N = ( invg ` G )


  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ ( A e. X /\ B e. Y /\ C e. Y ) ) -> ( ( A .(+) B ) = C <-> ( ( N ` A ) .(+) C ) = B ) )

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
    cC
    wceq
    #
    cB
    cA
    cN
    cfv
    #
    cC
    c.po
    co
    #
    wceq
    #
    @9
    cB
    wceq
    @5
    @6
    cA
    @9
    c.po
    co
    #
    wceq
    #
    @7
    @10
    @5
    @11
    cC
    @6
    @5
    cA
    @8
    cG
    cplusg
    cfv
    #
    co
    #
    cC
    c.po
    co
    #
    cG
    c0g
    cfv
    #
    cC
    c.po
    co
    #
    @11
    cC
    @5
    @14
    @16
    cC
    c.po
    @5
    cG
    cgrp
    wcel
    #
    @1
    @14
    @16
    wceq
    @0
    @18
    @4
    c.po
    cG
    cY
    gagrp
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cX
    @13
    cG
    cN
    cA
    @16
    galcan.1
    @13
    eqid
    #
    @16
    eqid
    #
    gacan.2
    grprinv
    syl2anc
    oveq1d
    @5
    @0
    @1
    @8
    cX
    wcel
    #
    @3
    @15
    @11
    wceq
    @0
    @4
    simpl
    #
    @20
    @5
    @18
    @1
    @23
    @19
    @20
    cX
    cG
    cN
    cA
    galcan.1
    gacan.2
    grpinvcl
    syl2anc
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    @8
    cC
    @13
    c.po
    cG
    cX
    cY
    galcan.1
    @21
    gaass
    syl13anc
    @5
    @0
    @3
    @17
    cC
    wceq
    @24
    @26
    cC
    c.po
    cG
    cY
    @16
    @22
    gagrpid
    syl2anc
    3eqtr3d
    eqeq2d
    @5
    @0
    @1
    @2
    @9
    cY
    wcel
    @12
    @10
    wb
    @24
    @20
    @0
    @1
    @2
    @3
    simpr2
    @5
    @8
    cC
    cY
    cX
    cY
    c.po
    @0
    cX
    cY
    cxp
    cY
    c.po
    wf
    @4
    c.po
    cG
    cX
    cY
    galcan.1
    gaf
    adantr
    @25
    @26
    fovrnd
    cA
    cB
    @9
    c.po
    cG
    cX
    cY
    galcan.1
    galcan
    syl13anc
    bitr3d
    cB
    @9
    eqcom
    syl6bb
end
