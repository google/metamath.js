include "cfv.mm"
include "csn.mm"
include "wne.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "nelne1.mm"
include "sylbi.mm"
include "syl.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochn0nv.mm"
include "mpbid.mm"

theorem dochsnkrlem1
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


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.0
    csn
    #
    wne
    #
    @1
    c.pe
    cfv
    cV
    wne
    wph
    cX
    @1
    @2
    cdif
    wcel
    #
    @3
    dochsnkr.x
    @4
    cX
    @1
    wcel
    cX
    @2
    wcel
    wn
    wa
    @3
    cX
    @1
    @2
    eldif
    cX
    @1
    @2
    nelne1
    sylbi
    syl
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    c.0
    dochsnkr.h
    dochsnkr.o
    dochsnkr.u
    dochsnkr.v
    dochsnkr.z
    dochsnkr.k
    wph
    cF
    cG
    cL
    cV
    cU
    dochsnkr.v
    dochsnkr.f
    dochsnkr.l
    wph
    cU
    cH
    cK
    cW
    dochsnkr.h
    dochsnkr.u
    dochsnkr.k
    dvhlmod
    dochsnkr.g
    lkrssv
    dochn0nv
    mpbid
end
