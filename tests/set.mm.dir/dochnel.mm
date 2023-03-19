include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "wne.mm"
include "cdif.mm"
include "lspsnid.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dochnel2.mm"
include "snssd.mm"
include "dochocsp.mm"
include "neleqtrd.mm"

theorem dochnel
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochnel.h: |- H = ( LHyp ` K )
  assume dochnel.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochnel.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochnel.v: |- V = ( Base ` U )
  assume dochnel.z: |- .0. = ( 0g ` U )
  assume dochnel.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochnel.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> -. X e. ( ._|_ ` { X } ) )

  proof
    wph
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
    c.pe
    cfv
    cX
    wph
    cU
    clss
    cfv
    #
    @2
    cU
    cH
    cK
    c.pe
    cW
    cX
    c.0
    dochnel.h
    dochnel.u
    @3
    eqid
    #
    dochnel.z
    dochnel.o
    dochnel.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @2
    @3
    wcel
    wph
    cU
    cH
    cK
    cW
    dochnel.h
    dochnel.u
    dochnel.k
    dvhlmod
    #
    wph
    cX
    cV
    c.0
    csn
    #
    dochnel.x
    eldifad
    #
    @3
    @1
    cV
    cU
    cX
    dochnel.v
    @4
    @1
    eqid
    #
    lspsncl
    syl2anc
    wph
    cX
    @2
    wcel
    #
    cX
    c.0
    wne
    #
    cX
    @2
    @8
    cdif
    wcel
    wph
    @5
    @6
    @11
    @7
    @9
    @1
    cV
    cU
    cX
    dochnel.v
    @10
    lspsnid
    syl2anc
    wph
    cX
    cV
    @8
    cdif
    wcel
    @12
    dochnel.x
    cX
    cV
    c.0
    eldifsni
    syl
    cX
    @2
    c.0
    eldifsn
    sylanbrc
    dochnel2
    wph
    cU
    cH
    cK
    @1
    c.pe
    cV
    cW
    @0
    dochnel.h
    dochnel.u
    dochnel.o
    dochnel.v
    @10
    dochnel.k
    wph
    cX
    cV
    @9
    snssd
    dochocsp
    neleqtrd
end
