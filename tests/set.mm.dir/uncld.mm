include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cuni.mm"
include "cdif.mm"
include "cin.mm"
include "difundi.mm"
include "ctop.mm"
include "cldrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "cldopn.mm"
include "adantl.mm"
include "inopn.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "wss.mm"
include "wb.mm"
include "cldss.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem uncld
  let cA: class A
  let cB: class B
  let cJ: class J
  let vx: setvar x
  let cS: class S


  assert |- ( ( A e. ( Clsd ` J ) /\ B e. ( Clsd ` J ) ) -> ( A u. B ) e. ( Clsd ` J ) )

  proof
    cA
    cJ
    ccld
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
    cun
    #
    @0
    wcel
    #
    cJ
    cuni
    #
    @4
    cdif
    #
    cJ
    wcel
    #
    @3
    @7
    @6
    cA
    cdif
    #
    @6
    cB
    cdif
    #
    cin
    #
    cJ
    @6
    cA
    cB
    difundi
    @3
    cJ
    ctop
    wcel
    #
    @9
    cJ
    wcel
    #
    @10
    cJ
    wcel
    #
    @11
    cJ
    wcel
    @1
    @12
    @2
    cA
    cJ
    cldrcl
    adantr
    #
    @1
    @13
    @2
    cA
    cJ
    @6
    @6
    eqid
    #
    cldopn
    adantr
    @2
    @14
    @1
    cB
    cJ
    @6
    @16
    cldopn
    adantl
    @9
    @10
    cJ
    inopn
    syl3anc
    syl5eqel
    @3
    @12
    @4
    @6
    wss
    #
    @5
    @8
    wb
    @15
    @3
    cA
    @6
    wss
    #
    cB
    @6
    wss
    #
    wa
    @17
    @1
    @18
    @2
    @19
    cA
    cJ
    @6
    @16
    cldss
    cB
    cJ
    @6
    @16
    cldss
    anim12i
    cA
    cB
    @6
    unss
    sylib
    @4
    cJ
    @6
    @16
    iscld2
    syl2anc
    mpbird
end
