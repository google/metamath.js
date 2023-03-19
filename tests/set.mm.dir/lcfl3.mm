include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "lcfl2.mm"
include "dochkrsat2.mm"
include "orbi1d.mm"
include "bitrd.mm"

theorem lcfl3
  let wph: wff ph
  let cA: class A
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
  assume lcfl3.h: |- H = ( LHyp ` K )
  assume lcfl3.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl3.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl3.v: |- V = ( Base ` U )
  assume lcfl3.a: |- A = ( LSAtoms ` U )
  assume lcfl3.f: |- F = ( LFnl ` U )
  assume lcfl3.l: |- L = ( LKer ` U )
  assume lcfl3.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl3.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( G e. C <-> ( ( ._|_ ` ( L ` G ) ) e. A \/ ( L ` G ) = V ) ) )

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
    #
    c.pe
    cfv
    cV
    wne
    #
    @0
    cV
    wceq
    #
    wo
    @1
    cA
    wcel
    #
    @3
    wo
    wph
    cC
    cU
    vf
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl3.h
    lcfl3.o
    lcfl3.u
    lcfl3.v
    lcfl3.f
    lcfl3.l
    lcfl3.c
    lcfl3.k
    lcfl3.g
    lcfl2
    wph
    @2
    @4
    @3
    wph
    cA
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl3.h
    lcfl3.o
    lcfl3.u
    lcfl3.v
    lcfl3.a
    lcfl3.f
    lcfl3.l
    lcfl3.k
    lcfl3.g
    dochkrsat2
    orbi1d
    bitrd
end
