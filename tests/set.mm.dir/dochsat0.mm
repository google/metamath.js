include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wne.mm"
include "dochkrsat.mm"
include "biimpd.mm"
include "necon1bd.mm"
include "orrd.mm"

theorem dochsat0
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let c.0: class .0.
  assume dochsat0.h: |- H = ( LHyp ` K )
  assume dochsat0.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsat0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsat0.z: |- .0. = ( 0g ` U )
  assume dochsat0.a: |- A = ( LSAtoms ` U )
  assume dochsat0.f: |- F = ( LFnl ` U )
  assume dochsat0.l: |- L = ( LKer ` U )
  assume dochsat0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsat0.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( L ` G ) ) e. A \/ ( ._|_ ` ( L ` G ) ) = { .0. } ) )

  proof
    wph
    cG
    cL
    cfv
    c.pe
    cfv
    #
    cA
    wcel
    #
    @0
    c.0
    csn
    #
    wceq
    wph
    @1
    @0
    @2
    wph
    @0
    @2
    wne
    @1
    wph
    cA
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    c.0
    dochsat0.h
    dochsat0.o
    dochsat0.u
    dochsat0.a
    dochsat0.f
    dochsat0.l
    dochsat0.z
    dochsat0.k
    dochsat0.g
    dochkrsat
    biimpd
    necon1bd
    orrd
end
