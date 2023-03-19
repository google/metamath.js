include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "cec.mm"
include "fneval.mm"
include "cvv.mm"
include "wer.mm"
include "fneer.mm"
include "a1i.mm"
include "elex.mm"
include "adantr.mm"
include "erth.mm"
include "tgtop.mm"
include "eqeqan12d.mm"
include "3bitr3d.mm"

theorem topfneec2
  let c.sm: class .~
  let cJ: class J
  let cK: class K
  assume topfneec2.1: |- .~ = ( Fne i^i `' Fne )


  assert |- ( ( J e. Top /\ K e. Top ) -> ( [ J ] .~ = [ K ] .~ <-> J = K ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cJ
    cK
    c.sm
    wbr
    cJ
    ctg
    cfv
    #
    cK
    ctg
    cfv
    #
    wceq
    cJ
    c.sm
    cec
    cK
    c.sm
    cec
    wceq
    cJ
    cK
    wceq
    cJ
    cK
    c.sm
    ctop
    ctop
    topfneec2.1
    fneval
    @2
    cJ
    cK
    c.sm
    cvv
    cvv
    c.sm
    wer
    @2
    c.sm
    topfneec2.1
    fneer
    a1i
    @0
    cJ
    cvv
    wcel
    @1
    cJ
    ctop
    elex
    adantr
    erth
    @0
    @1
    @3
    cJ
    @4
    cK
    cJ
    tgtop
    cK
    tgtop
    eqeqan12d
    3bitr3d
end
