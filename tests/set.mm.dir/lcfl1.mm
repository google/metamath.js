include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "biantrurd.mm"
include "lcfl1lem.mm"
include "syl6rbbr.mm"

theorem lcfl1
  let wph: wff ph
  let cC: class C
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cL: class L
  let c.pe: class ._|_
  assume lcfl1.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl1.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( G e. C <-> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @0
    wceq
    #
    cG
    cF
    wcel
    #
    @1
    wa
    cG
    cC
    wcel
    wph
    @2
    @1
    lcfl1.g
    biantrurd
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl1.c
    lcfl1lem
    syl6rbbr
end
