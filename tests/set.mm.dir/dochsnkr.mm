include "cfv.mm"
include "csn.mm"
include "clspn.mm"
include "clsa.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dochsnkrlem2.mm"
include "eldifad.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "lsatel.mm"
include "fveq2d.mm"
include "dochsnkrlem3.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ssdifssd.mm"
include "sseldd.mm"
include "snssd.mm"
include "dochocsp.mm"
include "3eqtr3d.mm"

theorem dochsnkr
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


  assert |- ( ph -> ( L ` G ) = ( ._|_ ` { X } ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    csn
    #
    cU
    clspn
    cfv
    #
    cfv
    #
    c.pe
    cfv
    @0
    @2
    c.pe
    cfv
    wph
    @1
    @4
    c.pe
    wph
    cU
    clsa
    cfv
    #
    @1
    @3
    cU
    cX
    c.0
    dochsnkr.z
    @3
    eqid
    #
    @5
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochsnkr.h
    dochsnkr.u
    dochsnkr.k
    dvhlvec
    wph
    @5
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
    @7
    dochsnkrlem2
    wph
    cX
    @1
    c.0
    csn
    #
    dochsnkr.x
    eldifad
    wph
    cX
    @1
    @8
    cdif
    #
    wcel
    cX
    c.0
    wne
    dochsnkr.x
    cX
    @1
    c.0
    eldifsni
    syl
    lsatel
    fveq2d
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
    dochsnkrlem3
    wph
    cU
    cH
    cK
    @3
    c.pe
    cV
    cW
    @2
    dochsnkr.h
    dochsnkr.u
    dochsnkr.o
    dochsnkr.v
    @6
    dochsnkr.k
    wph
    cX
    cV
    wph
    @9
    cV
    cX
    wph
    @1
    cV
    @8
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @0
    cV
    wss
    @1
    cV
    wss
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
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    dochsnkr.h
    dochsnkr.u
    dochsnkr.v
    dochsnkr.o
    dochssv
    syl2anc
    ssdifssd
    dochsnkr.x
    sseldd
    snssd
    dochocsp
    3eqtr3d
end
