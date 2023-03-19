include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "biantrurd.mm"
include "w3a.mm"
include "lcfls1lem.mm"
include "3anass.mm"
include "bitri.mm"
include "syl6rbbr.mm"

theorem lcfls1N
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cL: class L
  let c.pe: class ._|_
  assume lcfls1.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ Q ) }
  assume lcfls1.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  disjoint Q f
  assert |- ( ph -> ( G e. C <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) /\ ( ._|_ ` ( L ` G ) ) C_ Q ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @0
    wceq
    #
    @1
    cQ
    wss
    #
    wa
    #
    cG
    cF
    wcel
    #
    @4
    wa
    #
    cG
    cC
    wcel
    #
    wph
    @5
    @4
    lcfls1.g
    biantrurd
    @7
    @5
    @2
    @3
    w3a
    @6
    cC
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lcfls1.c
    lcfls1lem
    @5
    @2
    @3
    3anass
    bitri
    syl6rbbr
end
