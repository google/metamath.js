include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "clspn.mm"
include "eqid.mm"
include "dochocsn.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "dvh2dim.mm"
include "wceq.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "necon3bd.mm"
include "rexlimiv.mm"
include "syl.mm"
include "eqnetrd.mm"
include "snssd.mm"
include "dochn0nv.mm"
include "mpbird.mm"

theorem dochsnnz
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  assume dochsnnz.h: |- H = ( LHyp ` K )
  assume dochsnnz.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsnnz.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsnnz.v: |- V = ( Base ` U )
  assume dochsnnz.z: |- .0. = ( 0g ` U )
  assume dochsnnz.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsnnz.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ._|_ ` { X } ) =/= { .0. } )

  proof
    wph
    cX
    csn
    #
    c.pe
    cfv
    #
    c.0
    csn
    wne
    @1
    c.pe
    cfv
    #
    cV
    wne
    wph
    @2
    @0
    cU
    clspn
    cfv
    #
    cfv
    #
    cV
    wph
    cU
    cH
    cK
    @3
    c.pe
    cV
    cW
    cX
    dochsnnz.h
    dochsnnz.u
    dochsnnz.o
    dochsnnz.v
    @3
    eqid
    #
    dochsnnz.k
    dochsnnz.x
    dochocsn
    wph
    vy
    cv
    #
    @4
    wcel
    #
    wn
    #
    vy
    cV
    wrex
    @4
    cV
    wne
    #
    wph
    vy
    cU
    cH
    cK
    @3
    cV
    cW
    cX
    dochsnnz.h
    dochsnnz.u
    dochsnnz.v
    @5
    dochsnnz.k
    dochsnnz.x
    dvh2dim
    @8
    @9
    vy
    cV
    @6
    cV
    wcel
    #
    @7
    @4
    cV
    @4
    cV
    wceq
    @7
    @10
    @4
    cV
    @6
    eleq2
    biimprcd
    necon3bd
    rexlimiv
    syl
    eqnetrd
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    c.0
    dochsnnz.h
    dochsnnz.o
    dochsnnz.u
    dochsnnz.v
    dochsnnz.z
    dochsnnz.k
    wph
    cX
    cV
    dochsnnz.x
    snssd
    dochn0nv
    mpbird
end
