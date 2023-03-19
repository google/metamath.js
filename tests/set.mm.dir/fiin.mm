include "cfi.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "elfi.mm"
include "mpdan.mm"
include "ibi.mm"
include "adantr.mm"
include "simpr.mm"
include "ancoms.mm"
include "sylan.mm"
include "mpbid.mm"
include "wi.mm"
include "cun.mm"
include "elin.mm"
include "wss.mm"
include "elpwi.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "unfi.mm"
include "an4s.mm"
include "syl2anb.mm"
include "ineq12.mm"
include "intun.mm"
include "syl6eqr.mm"
include "inteq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "rexlimdvaa.mm"
include "rexlimiva.mm"
include "sylc.mm"
include "inex1g.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem fiin
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ( fi ` C ) /\ B e. ( fi ` C ) ) -> ( A i^i B ) e. ( fi ` C ) )

  proof
    cA
    cC
    cfi
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cin
    #
    @0
    wcel
    #
    @4
    vz
    cv
    #
    cint
    #
    wceq
    #
    vz
    cC
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @3
    cA
    vx
    cv
    #
    cint
    #
    wceq
    #
    vx
    @10
    wrex
    #
    cB
    vy
    cv
    #
    cint
    #
    wceq
    #
    vy
    @10
    wrex
    #
    @11
    @1
    @15
    @2
    @1
    @15
    @1
    cC
    cvv
    wcel
    #
    @1
    @15
    wb
    cA
    cC
    cfi
    elfvex
    #
    vx
    cA
    cC
    @0
    cvv
    elfi
    mpdan
    ibi
    adantr
    @3
    @2
    @19
    @1
    @2
    simpr
    @1
    @20
    @2
    @2
    @19
    wb
    #
    @21
    @2
    @20
    @22
    vy
    cB
    cC
    @0
    cvv
    elfi
    ancoms
    sylan
    mpbid
    @14
    @19
    @11
    wi
    vx
    @10
    @12
    @10
    wcel
    #
    @14
    wa
    @18
    @11
    vy
    @10
    @23
    @16
    @10
    wcel
    #
    @14
    @18
    @11
    @23
    @24
    wa
    #
    @12
    @16
    cun
    #
    @10
    wcel
    #
    @4
    @26
    cint
    #
    wceq
    #
    @11
    @14
    @18
    wa
    #
    @25
    @26
    @9
    wcel
    #
    @26
    cfn
    wcel
    #
    wa
    #
    @27
    @23
    @12
    @9
    wcel
    #
    @12
    cfn
    wcel
    #
    wa
    @16
    @9
    wcel
    #
    @16
    cfn
    wcel
    #
    wa
    @33
    @24
    @12
    @9
    cfn
    elin
    @16
    @9
    cfn
    elin
    @34
    @36
    @35
    @37
    @33
    @34
    @36
    wa
    #
    @31
    @35
    @37
    wa
    @32
    @38
    @26
    cC
    wss
    #
    @31
    @38
    @12
    cC
    wss
    #
    @16
    cC
    wss
    #
    wa
    @39
    @34
    @40
    @36
    @41
    @12
    cC
    elpwi
    @16
    cC
    elpwi
    anim12i
    @12
    @16
    cC
    unss
    sylib
    @26
    cC
    @12
    @16
    vx
    vex
    vy
    vex
    unex
    elpw
    sylibr
    @12
    @16
    unfi
    anim12i
    an4s
    syl2anb
    @26
    @9
    cfn
    elin
    sylibr
    @30
    @4
    @13
    @17
    cin
    @28
    cA
    @13
    cB
    @17
    ineq12
    @12
    @16
    intun
    syl6eqr
    @8
    @29
    vz
    @26
    @10
    @6
    @26
    wceq
    @7
    @28
    @4
    @6
    @26
    inteq
    eqeq2d
    rspcev
    syl2an
    an4s
    rexlimdvaa
    rexlimiva
    sylc
    @1
    @5
    @11
    wb
    #
    @2
    @1
    @4
    cvv
    wcel
    @20
    @42
    cA
    cB
    @0
    inex1g
    @21
    vz
    @4
    cC
    cvv
    cvv
    elfi
    syl2anc
    adantr
    mpbird
end
