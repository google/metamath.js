include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "cdih.mm"
include "eqid.mm"
include "chlt.mm"
include "wa.mm"
include "crn.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dochord3.mm"
include "snssd.mm"
include "dochocsp.mm"
include "sseq2d.mm"
include "3bitr3d.mm"
include "clss.mm"
include "dvhlmod.mm"
include "dochlss.mm"
include "lspsnel5.mm"
include "3bitr4d.mm"

theorem dochsncom
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dochsncom.h: |- H = ( LHyp ` K )
  assume dochsncom.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsncom.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsncom.v: |- V = ( Base ` U )
  assume dochsncom.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsncom.x: |- ( ph -> X e. V )
  assume dochsncom.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( X e. ( ._|_ ` { Y } ) <-> Y e. ( ._|_ ` { X } ) ) )

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
    cY
    csn
    #
    c.pe
    cfv
    #
    wss
    #
    @3
    @1
    cfv
    #
    @0
    c.pe
    cfv
    #
    wss
    #
    cX
    @4
    wcel
    cY
    @7
    wcel
    wph
    @2
    @6
    c.pe
    cfv
    #
    wss
    @6
    @2
    c.pe
    cfv
    #
    wss
    @5
    @8
    wph
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    c.pe
    cW
    @2
    @6
    dochsncom.h
    @11
    eqid
    #
    dochsncom.o
    dochsncom.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wcel
    @2
    @11
    crn
    #
    wcel
    dochsncom.k
    dochsncom.x
    cU
    cH
    @11
    cK
    @1
    cV
    cW
    cX
    dochsncom.h
    dochsncom.u
    dochsncom.v
    @1
    eqid
    #
    @12
    dihlsprn
    syl2anc
    wph
    @13
    cY
    cV
    wcel
    @6
    @14
    wcel
    dochsncom.k
    dochsncom.y
    cU
    cH
    @11
    cK
    @1
    cV
    cW
    cY
    dochsncom.h
    dochsncom.u
    dochsncom.v
    @15
    @12
    dihlsprn
    syl2anc
    dochord3
    wph
    @9
    @4
    @2
    wph
    cU
    cH
    cK
    @1
    c.pe
    cV
    cW
    @3
    dochsncom.h
    dochsncom.u
    dochsncom.o
    dochsncom.v
    @15
    dochsncom.k
    wph
    cY
    cV
    dochsncom.y
    snssd
    #
    dochocsp
    sseq2d
    wph
    @10
    @7
    @6
    wph
    cU
    cH
    cK
    @1
    c.pe
    cV
    cW
    @0
    dochsncom.h
    dochsncom.u
    dochsncom.o
    dochsncom.v
    @15
    dochsncom.k
    wph
    cX
    cV
    dochsncom.x
    snssd
    #
    dochocsp
    sseq2d
    3bitr3d
    wph
    cU
    clss
    cfv
    #
    @4
    @1
    cV
    cU
    cX
    dochsncom.v
    @18
    eqid
    #
    @15
    wph
    cU
    cH
    cK
    cW
    dochsncom.h
    dochsncom.u
    dochsncom.k
    dvhlmod
    #
    wph
    @13
    @3
    cV
    wss
    @4
    @18
    wcel
    dochsncom.k
    @16
    @18
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochsncom.h
    dochsncom.u
    dochsncom.v
    @19
    dochsncom.o
    dochlss
    syl2anc
    dochsncom.x
    lspsnel5
    wph
    @18
    @7
    @1
    cV
    cU
    cY
    dochsncom.v
    @19
    @15
    @20
    wph
    @13
    @0
    cV
    wss
    @7
    @18
    wcel
    dochsncom.k
    @17
    @18
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    dochsncom.h
    dochsncom.u
    dochsncom.v
    @19
    dochsncom.o
    dochlss
    syl2anc
    dochsncom.y
    lspsnel5
    3bitr4d
end
