include "c0.mm"
include "wne.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cuni.mm"
include "cdif.mm"
include "ciun.mm"
include "wceq.mm"
include "wss.mm"
include "eqid.mm"
include "cldss.mm"
include "dfss4.mm"
include "sylib.mm"
include "ralimi.mm"
include "iineq2.mm"
include "syl.mm"
include "adantl.mm"
include "iindif2.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "ctop.mm"
include "wrex.mm"
include "r19.2z.mm"
include "cldrcl.mm"
include "rexlimivw.mm"
include "cldopn.mm"
include "iunopn.mm"
include "syl2anc.mm"
include "opncld.mm"
include "eqeltrd.mm"

theorem iincld
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cS: class S

  disjoint A x
  disjoint J x
  disjoint S x
  assert |- ( ( A =/= (/) /\ A. x e. A B e. ( Clsd ` J ) ) -> |^|_ x e. A B e. ( Clsd ` J ) )

  proof
    cA
    c0
    wne
    #
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    ciin
    #
    cJ
    cuni
    #
    vx
    cA
    @6
    cB
    cdif
    #
    ciun
    #
    cdif
    #
    @1
    @4
    vx
    cA
    @6
    @7
    cdif
    #
    ciin
    #
    @5
    @9
    @3
    @11
    @5
    wceq
    #
    @0
    @3
    @10
    cB
    wceq
    #
    vx
    cA
    wral
    @12
    @2
    @13
    vx
    cA
    @2
    cB
    @6
    wss
    @13
    cB
    cJ
    @6
    @6
    eqid
    #
    cldss
    cB
    @6
    dfss4
    sylib
    ralimi
    vx
    cA
    @10
    cB
    iineq2
    syl
    adantl
    @0
    @11
    @9
    wceq
    @3
    vx
    cA
    @6
    @7
    iindif2
    adantr
    eqtr3d
    @4
    cJ
    ctop
    wcel
    #
    @8
    cJ
    wcel
    #
    @9
    @1
    wcel
    @4
    @2
    vx
    cA
    wrex
    @15
    @2
    vx
    cA
    r19.2z
    @2
    @15
    vx
    cA
    cB
    cJ
    cldrcl
    rexlimivw
    syl
    #
    @4
    @15
    @7
    cJ
    wcel
    #
    vx
    cA
    wral
    #
    @16
    @17
    @3
    @19
    @0
    @2
    @18
    vx
    cA
    cB
    cJ
    @6
    @14
    cldopn
    ralimi
    adantl
    vx
    cA
    @7
    cJ
    iunopn
    syl2anc
    @8
    cJ
    @6
    @14
    opncld
    syl2anc
    eqeltrd
end
