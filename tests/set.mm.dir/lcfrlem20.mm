include "cpr.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "clsm.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lsmpr.mm"
include "ineq1d.mm"
include "clss.mm"
include "clsh.mm"
include "dvhlvec.mm"
include "lcfrlem17.mm"
include "dochsnshp.mm"
include "lsatlspsn.mm"
include "wcel.mm"
include "wss.mm"
include "chlt.mm"
include "wa.mm"
include "clmod.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "snssd.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lspsnel5.mm"
include "mtbid.mm"
include "lshpat.mm"
include "eqeltrd.mm"

theorem lcfrlem20
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
  assume lcfrlem20.e: |- ( ph -> -. X e. ( ._|_ ` { ( X .+ Y ) } ) )


  assert |- ( ph -> ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) ) e. A )

  proof
    wph
    cX
    cY
    cpr
    cN
    cfv
    #
    cX
    cY
    c.pl
    co
    #
    csn
    #
    c.pe
    cfv
    #
    cin
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    #
    @3
    cin
    cA
    wph
    @0
    @7
    @3
    wph
    @6
    cN
    cV
    cU
    cX
    cY
    lcfrlem17.v
    lcfrlem17.n
    @6
    eqid
    #
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
    c.0
    csn
    #
    lcfrlem17.x
    eldifad
    #
    wph
    cY
    cV
    @10
    lcfrlem17.y
    eldifad
    #
    lsmpr
    ineq1d
    wph
    cA
    @6
    @4
    @5
    cU
    clss
    cfv
    #
    @3
    cU
    clsh
    cfv
    #
    cU
    @13
    eqid
    #
    @8
    @14
    eqid
    #
    lcfrlem17.a
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlvec
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    @14
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.z
    @16
    lcfrlem17.k
    wph
    cA
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem17
    dochsnshp
    wph
    cA
    cN
    cV
    cU
    cX
    c.0
    lcfrlem17.v
    lcfrlem17.n
    lcfrlem17.z
    lcfrlem17.a
    @9
    lcfrlem17.x
    lsatlspsn
    wph
    cA
    cN
    cV
    cU
    cY
    c.0
    lcfrlem17.v
    lcfrlem17.n
    lcfrlem17.z
    lcfrlem17.a
    @9
    lcfrlem17.y
    lsatlspsn
    lcfrlem17.ne
    wph
    cX
    @3
    wcel
    @4
    @3
    wss
    lcfrlem20.e
    wph
    @13
    @3
    cN
    cV
    cU
    cX
    lcfrlem17.v
    @15
    lcfrlem17.n
    @9
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    cV
    wss
    @3
    @13
    wcel
    lcfrlem17.k
    wph
    @1
    cV
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
    cV
    wcel
    @9
    @11
    @12
    c.pl
    cV
    cU
    cX
    cY
    lcfrlem17.v
    lcfrlem17.p
    lmodvacl
    syl3anc
    snssd
    @13
    cU
    cH
    cK
    c.pe
    cV
    cW
    @2
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @15
    lcfrlem17.o
    dochlss
    syl2anc
    @11
    lspsnel5
    mtbid
    lshpat
    eqeltrd
end
