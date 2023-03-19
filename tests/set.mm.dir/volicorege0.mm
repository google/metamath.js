include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "0red.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "volicore.mm"
include "cdm.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "simpr.mm"
include "icombl.mm"
include "syl2anc.mm"
include "volge0.mm"
include "syl.mm"
include "ltpnfd.mm"
include "elicod.mm"

theorem volicorege0
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A [,) B ) ) e. ( 0 [,) +oo ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cpnf
    cA
    cB
    cico
    co
    #
    cvol
    cfv
    #
    @2
    cc0
    @2
    0red
    rexrd
    cpnf
    cxr
    wcel
    @2
    pnfxr
    a1i
    @2
    @4
    cA
    cB
    volicore
    #
    rexrd
    @2
    @3
    cvol
    cdm
    wcel
    #
    cc0
    @4
    cle
    wbr
    @2
    @0
    cB
    cxr
    wcel
    @6
    @0
    @1
    simpl
    @2
    cB
    @0
    @1
    simpr
    rexrd
    cA
    cB
    icombl
    syl2anc
    @3
    volge0
    syl
    @2
    @4
    @5
    ltpnfd
    elicod
end
