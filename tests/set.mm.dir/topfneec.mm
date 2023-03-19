include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "ctop.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrel.mm"
include "wb.mm"
include "cvv.mm"
include "wer.mm"
include "fneer.mm"
include "errel.mm"
include "ax-mp.mm"
include "relelec.mm"
include "wi.mm"
include "brrelex2i.mm"
include "a1i.mm"
include "wa.mm"
include "ctb.mm"
include "eleq1.mm"
include "biimparc.mm"
include "tgclb.mm"
include "sylibr.mm"
include "elex.mm"
include "syl.mm"
include "ex.mm"
include "fneval.mm"
include "tgtop.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantr.mm"
include "bitrd.mm"
include "pm5.21ndd.mm"
include "syl5bb.mm"

theorem topfneec
  let cA: class A
  let c.sm: class .~
  let cJ: class J
  assume topfneec.1: |- .~ = ( Fne i^i `' Fne )


  assert |- ( J e. Top -> ( A e. [ J ] .~ <-> ( topGen ` A ) = J ) )

  proof
    cA
    cJ
    c.sm
    cec
    wcel
    #
    cJ
    cA
    c.sm
    wbr
    #
    cJ
    ctop
    wcel
    #
    cA
    ctg
    cfv
    #
    cJ
    wceq
    #
    c.sm
    wrel
    #
    @0
    @1
    wb
    cvv
    c.sm
    wer
    @5
    c.sm
    topfneec.1
    fneer
    cvv
    c.sm
    errel
    ax-mp
    #
    cA
    cJ
    c.sm
    relelec
    ax-mp
    @2
    cA
    cvv
    wcel
    #
    @1
    @4
    @1
    @7
    wi
    @2
    cJ
    cA
    c.sm
    @6
    brrelex2i
    a1i
    @2
    @4
    @7
    @2
    @4
    wa
    #
    cA
    ctb
    wcel
    #
    @7
    @8
    @3
    ctop
    wcel
    #
    @9
    @4
    @10
    @2
    @3
    cJ
    ctop
    eleq1
    biimparc
    cA
    tgclb
    sylibr
    cA
    ctb
    elex
    syl
    ex
    @2
    @7
    @1
    @4
    wb
    @2
    @7
    wa
    @1
    cJ
    ctg
    cfv
    #
    @3
    wceq
    #
    @4
    cJ
    cA
    c.sm
    ctop
    cvv
    topfneec.1
    fneval
    @2
    @12
    @4
    wb
    @7
    @2
    @12
    cJ
    @3
    wceq
    @4
    @2
    @11
    cJ
    @3
    cJ
    tgtop
    eqeq1d
    cJ
    @3
    eqcom
    syl6bb
    adantr
    bitrd
    ex
    pm5.21ndd
    syl5bb
end
