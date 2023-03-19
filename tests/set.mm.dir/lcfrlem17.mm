include "co.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lmodindp1.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem lcfrlem17
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( X .+ Y ) e. ( V \ { .0. } ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cV
    wcel
    #
    @0
    c.0
    wne
    @0
    cV
    c.0
    csn
    #
    cdif
    wcel
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @1
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    #
    wph
    cX
    cV
    @2
    lcfrlem17.x
    eldifad
    #
    wph
    cY
    cV
    @2
    lcfrlem17.y
    eldifad
    #
    c.pl
    cV
    cU
    cX
    cY
    lcfrlem17.v
    lcfrlem17.p
    lmodvacl
    syl3anc
    wph
    c.pl
    cN
    cV
    cU
    cX
    cY
    c.0
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    @3
    @4
    @5
    lcfrlem17.ne
    lmodindp1
    @0
    cV
    c.0
    eldifsn
    sylanbrc
end
