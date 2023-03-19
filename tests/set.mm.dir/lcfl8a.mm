include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "csn.mm"
include "wrex.mm"
include "eqid.mm"
include "lcfl1.mm"
include "lcfl8.mm"
include "bitr3d.mm"

theorem lcfl8a
  let wph: wff ph
  let vx: setvar x
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vf: setvar f
  assume lcfl8a.h: |- H = ( LHyp ` K )
  assume lcfl8a.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl8a.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl8a.v: |- V = ( Base ` U )
  assume lcfl8a.f: |- F = ( LFnl ` U )
  assume lcfl8a.l: |- L = ( LKer ` U )
  assume lcfl8a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl8a.g: |- ( ph -> G e. F )

  disjoint F x
  disjoint G x
  disjoint L x
  disjoint ._|_ x
  disjoint U x
  disjoint V x
  disjoint ph x
  disjoint f x
  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) <-> E. x e. V ( L ` G ) = ( ._|_ ` { x } ) ) )

  proof
    wph
    cG
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @0
    wceq
    vf
    cF
    crab
    #
    wcel
    cG
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @2
    wceq
    @2
    vx
    cv
    csn
    c.pe
    cfv
    wceq
    vx
    cV
    wrex
    wph
    @1
    vf
    cF
    cG
    cL
    c.pe
    @1
    eqid
    #
    lcfl8a.g
    lcfl1
    wph
    vx
    @1
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
    lcfl8a.h
    lcfl8a.o
    lcfl8a.u
    lcfl8a.v
    lcfl8a.f
    lcfl8a.l
    @3
    lcfl8a.k
    lcfl8a.g
    lcfl8
    bitr3d
end
