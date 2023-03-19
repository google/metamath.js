include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "lcfls1lem.mm"
include "lcfl1lem.mm"
include "anbi1i.mm"
include "3bitr4i.mm"

theorem lcfls1c
  let cC: class C
  let cD: class D
  let cQ: class Q
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cL: class L
  let c.pe: class ._|_
  assume lcfls1.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ Q ) }
  assume lcfls1c.c: |- D = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  disjoint Q f
  assert |- ( G e. C <-> ( G e. D /\ ( ._|_ ` ( L ` G ) ) C_ Q ) )

  proof
    cG
    cF
    wcel
    #
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @1
    wceq
    #
    @2
    cQ
    wss
    #
    w3a
    @0
    @3
    wa
    #
    @4
    wa
    cG
    cC
    wcel
    cG
    cD
    wcel
    #
    @4
    wa
    @0
    @3
    @4
    df-3an
    cC
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lcfls1.c
    lcfls1lem
    @6
    @5
    @4
    cD
    vf
    cF
    cG
    cL
    c.pe
    lcfls1c.c
    lcfl1lem
    anbi1i
    3bitr4i
end
