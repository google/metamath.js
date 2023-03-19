include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulm1.mm"
include "ad2antrr.mm"
include "ad2antrl.mm"
include "oveq12d.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "pm3.2i.mm"
include "angcan.mm"
include "mp3an3.mm"
include "eqtr3d.mm"

theorem angneg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( -u A F -u B ) = ( A F B ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    wa
    #
    c1
    cneg
    #
    cA
    cmul
    co
    #
    @7
    cB
    cmul
    co
    #
    cF
    co
    #
    cA
    cneg
    #
    cB
    cneg
    #
    cF
    co
    cA
    cB
    cF
    co
    #
    @6
    @8
    @11
    @9
    @12
    cF
    @0
    @8
    @11
    wceq
    @1
    @5
    cA
    mulm1
    ad2antrr
    @3
    @9
    @12
    wceq
    @2
    @4
    cB
    mulm1
    ad2antrl
    oveq12d
    @2
    @5
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    @10
    @13
    wceq
    @14
    @15
    neg1cn
    neg1ne0
    pm3.2i
    vx
    vy
    cA
    cB
    @7
    cF
    ang.1
    angcan
    mp3an3
    eqtr3d
end
