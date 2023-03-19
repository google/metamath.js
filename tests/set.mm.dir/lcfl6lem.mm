include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "c0g.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "sseldd.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dochflcl.mm"
include "dochsnkr.mm"
include "dochsnkr2.mm"
include "eqtr4d.mm"
include "dochfl1.mm"
include "dochfln0.mm"
include "eqlkr3.mm"

theorem lcfl6lem
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
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
  assume lcfl6lem.h: |- H = ( LHyp ` K )
  assume lcfl6lem.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl6lem.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl6lem.v: |- V = ( Base ` U )
  assume lcfl6lem.a: |- .+ = ( +g ` U )
  assume lcfl6lem.t: |- .x. = ( .s ` U )
  assume lcfl6lem.s: |- S = ( Scalar ` U )
  assume lcfl6lem.i: |- .1. = ( 1r ` S )
  assume lcfl6lem.r: |- R = ( Base ` S )
  assume lcfl6lem.z: |- .0. = ( 0g ` U )
  assume lcfl6lem.f: |- F = ( LFnl ` U )
  assume lcfl6lem.l: |- L = ( LKer ` U )
  assume lcfl6lem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl6lem.g: |- ( ph -> G e. F )
  assume lcfl6lem.x: |- ( ph -> X e. ( ( ._|_ ` ( L ` G ) ) \ { .0. } ) )
  assume lcfl6lem.y: |- ( ph -> ( G ` X ) = .1. )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint .1. k
  disjoint .1. w
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint V v
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint .0. w
  assert |- ( ph -> G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) ) )

  proof
    wph
    cR
    cS
    cF
    cG
    vv
    cV
    vv
    cv
    vw
    cv
    vk
    cv
    cX
    c.x
    co
    c.pl
    co
    wceq
    vw
    cX
    csn
    c.pe
    cfv
    #
    wrex
    vk
    cR
    crio
    cmpt
    #
    cL
    cV
    cU
    cX
    cS
    c0g
    cfv
    #
    lcfl6lem.v
    lcfl6lem.s
    lcfl6lem.r
    @2
    eqid
    #
    lcfl6lem.f
    lcfl6lem.l
    wph
    cU
    cH
    cK
    cW
    lcfl6lem.h
    lcfl6lem.u
    lcfl6lem.k
    dvhlvec
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    cV
    cX
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @4
    cV
    wss
    @5
    cV
    wss
    lcfl6lem.k
    wph
    cF
    cG
    cL
    cV
    cU
    lcfl6lem.v
    lcfl6lem.f
    lcfl6lem.l
    wph
    cU
    cH
    cK
    cW
    lcfl6lem.h
    lcfl6lem.u
    lcfl6lem.k
    dvhlmod
    lcfl6lem.g
    lkrssv
    cU
    cH
    cK
    c.pe
    cV
    cW
    @4
    lcfl6lem.h
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.o
    dochssv
    syl2anc
    wph
    cX
    @5
    c.0
    csn
    #
    lcfl6lem.x
    eldifad
    sseldd
    #
    lcfl6lem.g
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    cF
    @1
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    lcfl6lem.h
    lcfl6lem.o
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.z
    lcfl6lem.a
    lcfl6lem.t
    lcfl6lem.f
    lcfl6lem.s
    lcfl6lem.r
    @1
    eqid
    #
    lcfl6lem.k
    wph
    cX
    cV
    wcel
    cX
    c.0
    wne
    #
    cX
    cV
    @6
    cdif
    wcel
    @7
    wph
    cX
    @5
    @6
    cdif
    wcel
    @9
    lcfl6lem.x
    cX
    @5
    c.0
    eldifsni
    syl
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    #
    dochflcl
    wph
    @4
    @0
    @1
    cL
    cfv
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
    lcfl6lem.h
    lcfl6lem.o
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.z
    lcfl6lem.f
    lcfl6lem.l
    lcfl6lem.k
    lcfl6lem.g
    lcfl6lem.x
    dochsnkr
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    @1
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfl6lem.h
    lcfl6lem.o
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.z
    lcfl6lem.a
    lcfl6lem.t
    lcfl6lem.l
    lcfl6lem.s
    lcfl6lem.r
    @8
    lcfl6lem.k
    @10
    dochsnkr2
    eqtr4d
    wph
    cX
    cG
    cfv
    c.1
    cX
    @1
    cfv
    lcfl6lem.y
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    c.1
    vk
    @1
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    lcfl6lem.h
    lcfl6lem.o
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.a
    lcfl6lem.t
    lcfl6lem.z
    lcfl6lem.s
    lcfl6lem.r
    lcfl6lem.i
    lcfl6lem.k
    @10
    @8
    dochfl1
    eqtr4d
    wph
    cS
    cU
    cF
    cG
    cH
    cK
    cL
    @2
    c.pe
    cV
    cW
    cX
    c.0
    lcfl6lem.h
    lcfl6lem.o
    lcfl6lem.u
    lcfl6lem.v
    lcfl6lem.s
    @3
    lcfl6lem.z
    lcfl6lem.f
    lcfl6lem.l
    lcfl6lem.k
    lcfl6lem.g
    lcfl6lem.x
    dochfln0
    eqlkr3
end
