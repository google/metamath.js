include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "csupp.mm"
include "cfn.mm"
include "w3a.mm"
include "cun.mm"
include "cplusg.mm"
include "cof.mm"
include "wss.mm"
include "unfi.mm"
include "3ad2ant3.mm"
include "mndpsuppss.mm"
include "3adant3.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem mndpsuppfi
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume mndpsuppfi.r: |- R = ( Base ` M )


  assert |- ( ( ( M e. Mnd /\ V e. X ) /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) /\ ( ( A supp ( 0g ` M ) ) e. Fin /\ ( B supp ( 0g ` M ) ) e. Fin ) ) -> ( ( A oF ( +g ` M ) B ) supp ( 0g ` M ) ) e. Fin )

  proof
    cM
    cmnd
    wcel
    cV
    cX
    wcel
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    cB
    @1
    wcel
    wa
    #
    cA
    cM
    c0g
    cfv
    #
    csupp
    co
    #
    cfn
    wcel
    cB
    @3
    csupp
    co
    #
    cfn
    wcel
    wa
    #
    w3a
    @4
    @5
    cun
    #
    cfn
    wcel
    #
    cA
    cB
    cM
    cplusg
    cfv
    cof
    co
    @3
    csupp
    co
    #
    @7
    wss
    #
    @9
    cfn
    wcel
    @6
    @0
    @8
    @2
    @4
    @5
    unfi
    3ad2ant3
    @0
    @2
    @10
    @6
    cA
    cB
    cR
    cM
    cV
    cX
    mndpsuppfi.r
    mndpsuppss
    3adant3
    @7
    @9
    ssfi
    syl2anc
end
