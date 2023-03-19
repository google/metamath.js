include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wo.mm"
include "dochsnkrlem1.mm"
include "orcd.mm"
include "dochkrshp4.mm"
include "mpbird.mm"

theorem dochsnkrlem3
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochsnkr.h: |- H = ( LHyp ` K )
  assume dochsnkr.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsnkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsnkr.v: |- V = ( Base ` U )
  assume dochsnkr.z: |- .0. = ( 0g ` U )
  assume dochsnkr.f: |- F = ( LFnl ` U )
  assume dochsnkr.l: |- L = ( LKer ` U )
  assume dochsnkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsnkr.g: |- ( ph -> G e. F )
  assume dochsnkr.x: |- ( ph -> X e. ( ( ._|_ ` ( L ` G ) ) \ { .0. } ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) )

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
    #
    @0
    wceq
    @1
    cV
    wne
    #
    @0
    cV
    wceq
    #
    wo
    wph
    @2
    @3
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
    cX
    c.0
    dochsnkr.h
    dochsnkr.o
    dochsnkr.u
    dochsnkr.v
    dochsnkr.z
    dochsnkr.f
    dochsnkr.l
    dochsnkr.k
    dochsnkr.g
    dochsnkr.x
    dochsnkrlem1
    orcd
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
    dochsnkr.h
    dochsnkr.o
    dochsnkr.u
    dochsnkr.v
    dochsnkr.f
    dochsnkr.l
    dochsnkr.k
    dochsnkr.g
    dochkrshp4
    mpbird
end
