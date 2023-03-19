include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "lcfl1.mm"
include "cbs.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochoccl.mm"
include "bitr4d.mm"

theorem lcfl5
  let wph: wff ph
  let cC: class C
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  assume lcfl5.h: |- H = ( LHyp ` K )
  assume lcfl5.i: |- I = ( ( DIsoH ` K ) ` W )
  assume lcfl5.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl5.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl5.f: |- F = ( LFnl ` U )
  assume lcfl5.l: |- L = ( LKer ` U )
  assume lcfl5.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl5.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl5.g: |- ( ph -> G e. F )

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( G e. C <-> ( L ` G ) e. ran I ) )

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
    @0
    wceq
    @0
    cI
    crn
    wcel
    wph
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl5.c
    lcfl5.g
    lcfl1
    wph
    cU
    cH
    cI
    cK
    c.pe
    cU
    cbs
    cfv
    #
    cW
    @0
    lcfl5.h
    lcfl5.i
    lcfl5.u
    @1
    eqid
    #
    lcfl5.o
    lcfl5.k
    wph
    cF
    cG
    cL
    @1
    cU
    @2
    lcfl5.f
    lcfl5.l
    wph
    cU
    cH
    cK
    cW
    lcfl5.h
    lcfl5.u
    lcfl5.k
    dvhlmod
    lcfl5.g
    lkrssv
    dochoccl
    bitr4d
end
