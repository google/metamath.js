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
include "lshpkrcl.mm"

theorem dochflcl
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochflcl.h: |- H = ( LHyp ` K )
  assume dochflcl.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochflcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochflcl.v: |- V = ( Base ` U )
  assume dochflcl.z: |- .0. = ( 0g ` U )
  assume dochflcl.a: |- .+ = ( +g ` U )
  assume dochflcl.t: |- .x. = ( .s ` U )
  assume dochflcl.f: |- F = ( LFnl ` U )
  assume dochflcl.d: |- D = ( Scalar ` U )
  assume dochflcl.r: |- R = ( Base ` D )
  assume dochflcl.g: |- G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) )
  assume dochflcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochflcl.x: |- ( ph -> X e. ( V \ { .0. } ) )

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
  assert |- ( ph -> G e. F )

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
    cF
    cG
    cU
    clsh
    cfv
    #
    cR
    cU
    clspn
    cfv
    #
    cV
    cU
    cX
    dochflcl.v
    dochflcl.a
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
    dochflcl.h
    dochflcl.u
    dochflcl.k
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
    dochflcl.h
    dochflcl.o
    dochflcl.u
    dochflcl.v
    dochflcl.z
    @5
    dochflcl.k
    dochflcl.x
    dochsnshp
    wph
    cX
    cV
    c.0
    csn
    dochflcl.x
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
    dochflcl.h
    dochflcl.o
    dochflcl.u
    dochflcl.v
    dochflcl.z
    @3
    @4
    dochflcl.k
    dochflcl.x
    dochexmidat
    dochflcl.d
    dochflcl.r
    dochflcl.t
    dochflcl.g
    dochflcl.f
    lshpkrcl
end
