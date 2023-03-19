include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "eqid.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "dochsnkr2.mm"
include "snssd.mm"
include "dochocsp.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "dihlsprn.mm"
include "dochoc.mm"
include "eqtr2d.mm"
include "eleqtrd.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem dochsnkr2cl
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
  assert |- ( ph -> X e. ( ( ._|_ ` ( L ` G ) ) \ { .0. } ) )

  proof
    wph
    cX
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    wcel
    cX
    c.0
    wne
    #
    cX
    @1
    c.0
    csn
    #
    cdif
    wcel
    wph
    cX
    cX
    csn
    #
    cU
    clspn
    cfv
    #
    cfv
    #
    @1
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    #
    cX
    @6
    wcel
    wph
    cU
    cH
    cK
    cW
    dochsnkr2.h
    dochsnkr2.u
    dochsnkr2.k
    dvhlmod
    wph
    cX
    cV
    @3
    dochsnkr2.x
    eldifad
    #
    @5
    cV
    cU
    cX
    dochsnkr2.v
    @5
    eqid
    #
    lspsnid
    syl2anc
    wph
    @1
    @6
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @6
    wph
    @0
    @10
    c.pe
    wph
    @0
    @4
    c.pe
    cfv
    @10
    wph
    vw
    vv
    cD
    c.pl
    cR
    c.x
    cU
    vk
    cG
    cH
    cK
    cL
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
    dochsnkr2.a
    dochsnkr2.t
    dochsnkr2.l
    dochsnkr2.d
    dochsnkr2.r
    dochsnkr2.g
    dochsnkr2.k
    dochsnkr2.x
    dochsnkr2
    wph
    cU
    cH
    cK
    @5
    c.pe
    cV
    cW
    @4
    dochsnkr2.h
    dochsnkr2.u
    dochsnkr2.o
    dochsnkr2.v
    @9
    dochsnkr2.k
    wph
    cX
    cV
    @8
    snssd
    dochocsp
    eqtr4d
    fveq2d
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @6
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @11
    @6
    wceq
    dochsnkr2.k
    wph
    @12
    @7
    @14
    dochsnkr2.k
    @8
    cU
    cH
    @13
    cK
    @5
    cV
    cW
    cX
    dochsnkr2.h
    dochsnkr2.u
    dochsnkr2.v
    @9
    @13
    eqid
    #
    dihlsprn
    syl2anc
    cH
    @13
    cK
    c.pe
    cW
    @6
    dochsnkr2.h
    @15
    dochsnkr2.o
    dochoc
    syl2anc
    eqtr2d
    eleqtrd
    wph
    cX
    cV
    @3
    cdif
    wcel
    @2
    dochsnkr2.x
    cX
    cV
    c.0
    eldifsni
    syl
    cX
    @1
    c.0
    eldifsn
    sylanbrc
end
