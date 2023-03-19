include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "cdif.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ssdifd.mm"
include "sseldd.mm"
include "dochnel.mm"
include "wceq.mm"
include "eldifad.mm"
include "biantrurd.mm"
include "clmod.mm"
include "wb.mm"
include "ellkr.mm"
include "dochsnkr.mm"
include "eleq2d.mm"
include "3bitr2rd.mm"
include "necon3bbid.mm"
include "mpbid.mm"

theorem dochfln0
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochfln0.h: |- H = ( LHyp ` K )
  assume dochfln0.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochfln0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochfln0.v: |- V = ( Base ` U )
  assume dochfln0.r: |- R = ( Scalar ` U )
  assume dochfln0.n: |- N = ( 0g ` R )
  assume dochfln0.z: |- .0. = ( 0g ` U )
  assume dochfln0.f: |- F = ( LFnl ` U )
  assume dochfln0.l: |- L = ( LKer ` U )
  assume dochfln0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochfln0.g: |- ( ph -> G e. F )
  assume dochfln0.x: |- ( ph -> X e. ( ( ._|_ ` ( L ` G ) ) \ { .0. } ) )


  assert |- ( ph -> ( G ` X ) =/= N )

  proof
    wph
    cX
    cX
    csn
    c.pe
    cfv
    #
    wcel
    #
    wn
    cX
    cG
    cfv
    #
    cN
    wne
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    dochfln0.h
    dochfln0.o
    dochfln0.u
    dochfln0.v
    dochfln0.z
    dochfln0.k
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
    cdif
    cV
    @5
    cdif
    cX
    wph
    @4
    cV
    @5
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    cV
    wss
    @4
    cV
    wss
    dochfln0.k
    wph
    cF
    cG
    cL
    cV
    cU
    dochfln0.v
    dochfln0.f
    dochfln0.l
    wph
    cU
    cH
    cK
    cW
    dochfln0.h
    dochfln0.u
    dochfln0.k
    dvhlmod
    #
    dochfln0.g
    lkrssv
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochfln0.h
    dochfln0.u
    dochfln0.v
    dochfln0.o
    dochssv
    syl2anc
    #
    ssdifd
    dochfln0.x
    sseldd
    dochnel
    wph
    @1
    @2
    cN
    wph
    @2
    cN
    wceq
    #
    cX
    cV
    wcel
    #
    @8
    wa
    #
    cX
    @3
    wcel
    #
    @1
    wph
    @9
    @8
    wph
    @4
    cV
    cX
    @7
    wph
    cX
    @4
    @5
    dochfln0.x
    eldifad
    sseldd
    biantrurd
    wph
    cU
    clmod
    wcel
    cG
    cF
    wcel
    @11
    @10
    wb
    @6
    dochfln0.g
    cR
    cF
    cG
    cL
    cV
    cU
    cX
    clmod
    cN
    dochfln0.v
    dochfln0.r
    dochfln0.n
    dochfln0.f
    dochfln0.l
    ellkr
    syl2anc
    wph
    @3
    @0
    cX
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
    dochfln0.h
    dochfln0.o
    dochfln0.u
    dochfln0.v
    dochfln0.z
    dochfln0.f
    dochfln0.l
    dochfln0.k
    dochfln0.g
    dochfln0.x
    dochsnkr
    eleq2d
    3bitr2rd
    necon3bbid
    mpbid
end
