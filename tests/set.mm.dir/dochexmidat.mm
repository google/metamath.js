include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "dochnel.mm"
include "clsh.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dochsnshp.mm"
include "eldifad.mm"
include "lshpnelb.mm"
include "mpbid.mm"

theorem dochexmidat
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochexmidat.h: |- H = ( LHyp ` K )
  assume dochexmidat.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidat.v: |- V = ( Base ` U )
  assume dochexmidat.z: |- .0. = ( 0g ` U )
  assume dochexmidat.r: |- N = ( LSpan ` U )
  assume dochexmidat.p: |- .(+) = ( LSSum ` U )
  assume dochexmidat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidat.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( ( ._|_ ` { X } ) .(+) ( N ` { X } ) ) = V )

  proof
    wph
    cX
    cX
    csn
    #
    c.pe
    cfv
    #
    wcel
    wn
    @1
    @0
    cN
    cfv
    c.po
    co
    cV
    wceq
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    dochexmidat.h
    dochexmidat.o
    dochexmidat.u
    dochexmidat.v
    dochexmidat.z
    dochexmidat.k
    dochexmidat.x
    dochnel
    wph
    c.po
    @1
    cU
    clsh
    cfv
    #
    cN
    cV
    cU
    cX
    dochexmidat.v
    dochexmidat.r
    dochexmidat.p
    @2
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochexmidat.h
    dochexmidat.u
    dochexmidat.k
    dvhlvec
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @2
    c.0
    dochexmidat.h
    dochexmidat.o
    dochexmidat.u
    dochexmidat.v
    dochexmidat.z
    @3
    dochexmidat.k
    dochexmidat.x
    dochsnshp
    wph
    cX
    cV
    c.0
    csn
    dochexmidat.x
    eldifad
    lshpnelb
    mpbid
end
