include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wo.mm"
include "lcfl1.mm"
include "dochkrshp4.mm"
include "bitrd.mm"

theorem lcfl2
  let wph: wff ph
  let cC: class C
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume lcfl2.h: |- H = ( LHyp ` K )
  assume lcfl2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl2.v: |- V = ( Base ` U )
  assume lcfl2.f: |- F = ( LFnl ` U )
  assume lcfl2.l: |- L = ( LKer ` U )
  assume lcfl2.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl2.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( G e. C <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V \/ ( L ` G ) = V ) ) )

  proof
    wph
    cG
    cC
    wcel
    cG
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    #
    @0
    wceq
    @1
    cV
    wne
    @0
    cV
    wceq
    wo
    wph
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl2.c
    lcfl2.g
    lcfl1
    wph
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl2.h
    lcfl2.o
    lcfl2.u
    lcfl2.v
    lcfl2.f
    lcfl2.l
    lcfl2.k
    lcfl2.g
    dochkrshp4
    bitrd
end
