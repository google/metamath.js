include "wcel.mm"
include "cfv.mm"
include "clsa.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "lcfl3.mm"
include "clss.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "dochsatshpb.mm"
include "orbi1d.mm"
include "bitrd.mm"

theorem lcfl4N
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
  let cY: class Y
  assume lcfl4.h: |- H = ( LHyp ` K )
  assume lcfl4.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl4.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl4.v: |- V = ( Base ` U )
  assume lcfl4.y: |- Y = ( LSHyp ` U )
  assume lcfl4.f: |- F = ( LFnl ` U )
  assume lcfl4.l: |- L = ( LKer ` U )
  assume lcfl4.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl4.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( G e. C <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) e. Y \/ ( L ` G ) = V ) ) )

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
    cU
    clsa
    cfv
    #
    wcel
    #
    @0
    cV
    wceq
    #
    wo
    @1
    c.pe
    cfv
    cY
    wcel
    #
    @4
    wo
    wph
    @2
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
    lcfl4.h
    lcfl4.o
    lcfl4.u
    lcfl4.v
    @2
    eqid
    #
    lcfl4.f
    lcfl4.l
    lcfl4.c
    lcfl4.k
    lcfl4.g
    lcfl3
    wph
    @3
    @5
    @4
    wph
    @2
    @1
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    c.pe
    cW
    cY
    lcfl4.h
    lcfl4.o
    lcfl4.u
    @7
    eqid
    #
    @6
    lcfl4.y
    lcfl4.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @0
    cV
    wss
    @1
    @7
    wcel
    lcfl4.k
    wph
    cF
    cG
    cL
    cV
    cU
    lcfl4.v
    lcfl4.f
    lcfl4.l
    wph
    cU
    cH
    cK
    cW
    lcfl4.h
    lcfl4.u
    lcfl4.k
    dvhlmod
    lcfl4.g
    lkrssv
    @7
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    lcfl4.h
    lcfl4.u
    lcfl4.v
    @8
    lcfl4.o
    dochlss
    syl2anc
    dochsatshpb
    orbi1d
    bitrd
end
