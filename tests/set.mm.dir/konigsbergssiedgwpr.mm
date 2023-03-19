include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cpw.mm"
include "crab.mm"
include "wa.mm"
include "konigsbergiedgw.mm"
include "jctr.mm"
include "ccatrcl1.mm"
include "syl3an3.mm"

theorem konigsbergssiedgwpr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.

  disjoint V x
  assert |- ( ( A e. Word _V /\ B e. Word _V /\ E = ( A ++ B ) ) -> A e. Word { x e. ~P V | ( # ` x ) = 2 } )

  proof
    cE
    cA
    cB
    cconcat
    co
    wceq
    #
    cA
    cvv
    cword
    #
    wcel
    cB
    @1
    wcel
    @0
    cE
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    crab
    #
    cword
    #
    wcel
    #
    wa
    cA
    @3
    wcel
    @0
    @4
    vx
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergiedgw
    jctr
    cA
    cB
    @2
    cE
    cvv
    cvv
    ccatrcl1
    syl3an3
end
