include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "crn.mm"
include "eqid.mm"
include "lcfl1.mm"
include "lcfl5.mm"
include "bitr3d.mm"

theorem lcfl5a
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let vf: setvar f
  assume lcfl5a.h: |- H = ( LHyp ` K )
  assume lcfl5a.i: |- I = ( ( DIsoH ` K ) ` W )
  assume lcfl5a.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl5a.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl5a.f: |- F = ( LFnl ` U )
  assume lcfl5a.l: |- L = ( LKer ` U )
  assume lcfl5a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl5a.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) <-> ( L ` G ) e. ran I ) )

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
    cI
    crn
    wcel
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
    lcfl5a.g
    lcfl1
    wph
    @1
    cU
    vf
    cF
    cG
    cH
    cI
    cK
    cL
    c.pe
    cW
    lcfl5a.h
    lcfl5a.i
    lcfl5a.o
    lcfl5a.u
    lcfl5a.f
    lcfl5a.l
    @3
    lcfl5a.k
    lcfl5a.g
    lcfl5
    bitr3d
end
