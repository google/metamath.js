include "clsm.mm"
include "cfv.mm"
include "csn.mm"
include "clsh.mm"
include "clspn.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dochsnshp.mm"
include "eldifad.mm"
include "dochexmidat.mm"
include "lshpkr.mm"

theorem dochsnkr2
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochsnkr2.h: |- H = ( LHyp ` K )
  assume dochsnkr2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsnkr2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsnkr2.v: |- V = ( Base ` U )
  assume dochsnkr2.z: |- .0. = ( 0g ` U )
  assume dochsnkr2.a: |- .+ = ( +g ` U )
  assume dochsnkr2.t: |- .x. = ( .s ` U )
  assume dochsnkr2.l: |- L = ( LKer ` U )
  assume dochsnkr2.d: |- D = ( Scalar ` U )
  assume dochsnkr2.r: |- R = ( Base ` D )
  assume dochsnkr2.g: |- G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) )
  assume dochsnkr2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsnkr2.x: |- ( ph -> X e. ( V \ { .0. } ) )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint D k
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint R k
  disjoint R v
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint V v
  disjoint X k
  disjoint X v
  disjoint X w
  assert |- ( ph -> ( L ` G ) = ( ._|_ ` { X } ) )

  proof
    wph
    vv
    vw
    cD
    c.pl
    cU
    clsm
    cfv
    #
    c.x
    cX
    csn
    c.pe
    cfv
    vk
    cG
    cU
    clsh
    cfv
    #
    cR
    cL
    cU
    clspn
    cfv
    #
    cV
    cU
    cX
    dochsnkr2.v
    dochsnkr2.a
    @2
    eqid
    #
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochsnkr2.h
    dochsnkr2.u
    dochsnkr2.k
    dvhlvec
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @1
    c.0
    dochsnkr2.h
    dochsnkr2.o
    dochsnkr2.u
    dochsnkr2.v
    dochsnkr2.z
    @5
    dochsnkr2.k
    dochsnkr2.x
    dochsnshp
    wph
    cX
    cV
    c.0
    csn
    dochsnkr2.x
    eldifad
    wph
    @0
    cU
    cH
    cK
    @2
    c.pe
    cV
    cW
    cX
    c.0
    dochsnkr2.h
    dochsnkr2.o
    dochsnkr2.u
    dochsnkr2.v
    dochsnkr2.z
    @3
    @4
    dochsnkr2.k
    dochsnkr2.x
    dochexmidat
    dochsnkr2.d
    dochsnkr2.r
    dochsnkr2.t
    dochsnkr2.g
    dochsnkr2.l
    lshpkr
end
