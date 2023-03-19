include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "neii1.mm"
include "ssinss1.mm"
include "syl.mm"
include "3adant3.mm"
include "neii2.mm"
include "anim12dan.mm"
include "wi.mm"
include "inopn.mm"
include "3expa.mm"
include "ssin.mm"
include "biimpi.mm"
include "ss2in.mm"
include "anim12i.mm"
include "an4s.mm"
include "wceq.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "expr.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "ex.mm"
include "imp32.mm"
include "syldan.mm"
include "3impb.mm"
include "wb.mm"
include "neiss2.mm"
include "isnei.mm"
include "mpbir2and.mm"

theorem innei
  let cS: class S
  let cJ: class J
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) /\ M e. ( ( nei ` J ) ` S ) ) -> ( N i^i M ) e. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    cM
    @1
    wcel
    #
    w3a
    cN
    cM
    cin
    #
    @1
    wcel
    #
    @4
    cJ
    cuni
    #
    wss
    #
    cS
    vg
    cv
    #
    wss
    #
    @8
    @4
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    @0
    @2
    @7
    @3
    @0
    @2
    wa
    cN
    @6
    wss
    @7
    cS
    cJ
    cN
    @6
    @6
    eqid
    #
    neii1
    cN
    cM
    @6
    ssinss1
    syl
    3adant3
    @0
    @2
    @3
    @12
    @0
    @2
    @3
    wa
    cS
    vh
    cv
    #
    wss
    #
    @14
    cN
    wss
    #
    wa
    #
    vh
    cJ
    wrex
    #
    cS
    vv
    cv
    #
    wss
    #
    @19
    cM
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wa
    @12
    @0
    @2
    @18
    @3
    @23
    cS
    vh
    cJ
    cN
    neii2
    cS
    vv
    cJ
    cM
    neii2
    anim12dan
    @0
    @18
    @23
    @12
    @0
    @17
    @23
    @12
    wi
    #
    vh
    cJ
    @0
    @14
    cJ
    wcel
    #
    wa
    #
    @17
    @24
    @26
    @17
    wa
    @22
    @12
    vv
    cJ
    @26
    @19
    cJ
    wcel
    #
    @17
    @22
    @12
    wi
    @26
    @27
    wa
    #
    @17
    @22
    @12
    @28
    @14
    @19
    cin
    #
    cJ
    wcel
    #
    cS
    @29
    wss
    #
    @29
    @4
    wss
    #
    wa
    #
    @12
    @17
    @22
    wa
    @0
    @25
    @27
    @30
    @14
    @19
    cJ
    inopn
    3expa
    @15
    @20
    @16
    @21
    @33
    @15
    @20
    wa
    #
    @31
    @16
    @21
    wa
    @32
    @34
    @31
    cS
    @14
    @19
    ssin
    biimpi
    @14
    cN
    @19
    cM
    ss2in
    anim12i
    an4s
    @11
    @33
    vg
    @29
    cJ
    @8
    @29
    wceq
    @9
    @31
    @10
    @32
    @8
    @29
    cS
    sseq2
    @8
    @29
    @4
    sseq1
    anbi12d
    rspcev
    syl2an
    expr
    an32s
    rexlimdva
    ex
    rexlimdva
    imp32
    syldan
    3impb
    @0
    @2
    @5
    @7
    @12
    wa
    wb
    #
    @3
    @0
    @2
    cS
    @6
    wss
    @35
    cS
    cJ
    cN
    @6
    @13
    neiss2
    cS
    vg
    cJ
    @4
    @6
    @13
    isnei
    syldan
    3adant3
    mpbir2and
end
