include "cun.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "chil.mm"
include "wss.mm"
include "csh.mm"
include "wcel.mm"
include "spancl.mm"
include "ax-mp.mm"
include "shscli.mm"
include "shssii.mm"
include "spanss2.mm"
include "unss12.mm"
include "mp2an.mm"
include "shunssi.mm"
include "sstri.mm"
include "spanss.mm"
include "wceq.mm"
include "spanid.mm"
include "sseqtri.mm"
include "cv.mm"
include "wa.mm"
include "cva.mm"
include "wex.mm"
include "wrex.mm"
include "shseli.mm"
include "r2ex.mm"
include "bitri.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "vex.mm"
include "elspani.mm"
include "anbi12i.mm"
include "r19.26.mm"
include "bitr4i.mm"
include "r19.27v.mm"
include "sylanb.mm"
include "unss.mm"
include "prth.mm"
include "syl5bir.mm"
include "shaddcl.mm"
include "3expib.mm"
include "sylan9r.mm"
include "eleq1.mm"
include "biimprd.mm"
include "sylan9.mm"
include "expl.mm"
include "ralimia.mm"
include "unssi.mm"
include "sylibr.mm"
include "syl.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem spanuni
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume spanun.1: |- A C_ ~H
  assume spanun.2: |- B C_ ~H


  assert |- ( span ` ( A u. B ) ) = ( ( span ` A ) +H ( span ` B ) )

  proof
    cA
    cB
    cun
    #
    cspn
    cfv
    #
    cA
    cspn
    cfv
    #
    cB
    cspn
    cfv
    #
    cph
    co
    #
    @1
    @4
    cspn
    cfv
    #
    @4
    @4
    chil
    wss
    @0
    @4
    wss
    @1
    @5
    wss
    @4
    @2
    @3
    cA
    chil
    wss
    #
    @2
    csh
    wcel
    spanun.1
    cA
    spancl
    ax-mp
    #
    cB
    chil
    wss
    #
    @3
    csh
    wcel
    spanun.2
    cB
    spancl
    ax-mp
    #
    shscli
    #
    shssii
    @0
    @2
    @3
    cun
    #
    @4
    cA
    @2
    wss
    #
    cB
    @3
    wss
    #
    @0
    @11
    wss
    @6
    @12
    spanun.1
    cA
    spanss2
    ax-mp
    @8
    @13
    spanun.2
    cB
    spanss2
    ax-mp
    cA
    @2
    cB
    @3
    unss12
    mp2an
    @2
    @3
    @7
    @9
    shunssi
    sstri
    @0
    @4
    spanss
    mp2an
    @4
    csh
    wcel
    @5
    @4
    wceq
    @10
    @4
    spanid
    ax-mp
    sseqtri
    vx
    @4
    @1
    vx
    cv
    #
    @4
    wcel
    #
    vz
    cv
    #
    @2
    wcel
    #
    vw
    cv
    #
    @3
    wcel
    #
    wa
    #
    @14
    @16
    @18
    cva
    co
    #
    wceq
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    @14
    @1
    wcel
    #
    @15
    @22
    vw
    @3
    wrex
    vz
    @2
    wrex
    @24
    vz
    vw
    @2
    @3
    @14
    @7
    @9
    shseli
    @22
    vz
    vw
    @2
    @3
    r2ex
    bitri
    @23
    @25
    vz
    vw
    @23
    cA
    vy
    cv
    #
    wss
    #
    vz
    vy
    wel
    #
    wi
    #
    cB
    @26
    wss
    #
    vw
    vy
    wel
    #
    wi
    #
    wa
    #
    @22
    wa
    #
    vy
    csh
    wral
    #
    @25
    @20
    @33
    vy
    csh
    wral
    #
    @22
    @35
    @20
    @29
    vy
    csh
    wral
    #
    @32
    vy
    csh
    wral
    #
    wa
    @36
    @17
    @37
    @19
    @38
    @6
    @17
    @37
    wb
    spanun.1
    vy
    cA
    @16
    vz
    vex
    elspani
    ax-mp
    @8
    @19
    @38
    wb
    spanun.2
    vy
    cB
    @18
    vw
    vex
    elspani
    ax-mp
    anbi12i
    @29
    @32
    vy
    csh
    r19.26
    bitr4i
    @33
    @22
    vy
    csh
    r19.27v
    sylanb
    @35
    @0
    @26
    wss
    #
    vx
    vy
    wel
    #
    wi
    #
    vy
    csh
    wral
    #
    @25
    @34
    @41
    vy
    csh
    @26
    csh
    wcel
    #
    @33
    @22
    @41
    @43
    @33
    wa
    @39
    @21
    @26
    wcel
    #
    @22
    @40
    @33
    @39
    @28
    @31
    wa
    #
    @43
    @44
    @39
    @27
    @30
    wa
    @33
    @45
    cA
    cB
    @26
    unss
    @27
    @28
    @30
    @31
    prth
    syl5bir
    @43
    @28
    @31
    @44
    @16
    @18
    @26
    shaddcl
    3expib
    sylan9r
    @22
    @40
    @44
    @14
    @21
    @26
    eleq1
    biimprd
    sylan9
    expl
    ralimia
    @0
    chil
    wss
    @25
    @42
    wb
    cA
    cB
    chil
    spanun.1
    spanun.2
    unssi
    vy
    @0
    @14
    vx
    vex
    elspani
    ax-mp
    sylibr
    syl
    exlimivv
    sylbi
    ssriv
    eqssi
end
