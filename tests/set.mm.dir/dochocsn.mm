include "csn.mm"
include "cfv.mm"
include "snssd.mm"
include "dochocsp.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "eqtr3d.mm"

theorem dochocsn
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume dochocsn.h: |- H = ( LHyp ` K )
  assume dochocsn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochocsn.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochocsn.v: |- V = ( Base ` U )
  assume dochocsn.n: |- N = ( LSpan ` U )
  assume dochocsn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochocsn.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` { X } ) ) = ( N ` { X } ) )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @0
    c.pe
    cfv
    #
    c.pe
    cfv
    @1
    wph
    @2
    @4
    c.pe
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @0
    dochocsn.h
    dochocsn.u
    dochocsn.o
    dochocsn.v
    dochocsn.n
    dochocsn.k
    wph
    cX
    cV
    dochocsn.x
    snssd
    dochocsp
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
    @1
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @3
    @1
    wceq
    dochocsn.k
    wph
    @5
    cX
    cV
    wcel
    @7
    dochocsn.k
    dochocsn.x
    cU
    cH
    @6
    cK
    cN
    cV
    cW
    cX
    dochocsn.h
    dochocsn.u
    dochocsn.v
    dochocsn.n
    @6
    eqid
    #
    dihlsprn
    syl2anc
    cH
    @6
    cK
    c.pe
    cW
    @1
    dochocsn.h
    @8
    dochocsn.o
    dochoc
    syl2anc
    eqtr3d
end
