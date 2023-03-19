include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "lcfrlem17.mm"
include "dochnel.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "chlt.mm"
include "wss.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "snssd.mm"
include "eqid.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lssvacl.mm"
include "syl21anc.mm"
include "mtand.mm"
include "ianor.mm"
include "sylib.mm"

theorem lcfrlem19
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


  assert |- ( ph -> ( -. X e. ( ._|_ ` { ( X .+ Y ) } ) \/ -. Y e. ( ._|_ ` { ( X .+ Y ) } ) ) )

  proof
    wph
    cX
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
    wcel
    #
    cY
    @2
    wcel
    #
    wa
    #
    wn
    @3
    wn
    @4
    wn
    wo
    wph
    @5
    @0
    @2
    wcel
    #
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.z
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
    dochnel
    wph
    @5
    wa
    cU
    clmod
    wcel
    #
    @2
    cU
    clss
    cfv
    #
    wcel
    #
    @5
    @6
    wph
    @7
    @5
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
    adantr
    wph
    @9
    @5
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    cV
    wss
    @9
    lcfrlem17.k
    wph
    @0
    cV
    wph
    @7
    cX
    cV
    wcel
    cY
    cV
    wcel
    @0
    cV
    wcel
    @10
    wph
    cX
    cV
    c.0
    csn
    #
    lcfrlem17.x
    eldifad
    wph
    cY
    cV
    @11
    lcfrlem17.y
    eldifad
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
    @8
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @8
    eqid
    #
    lcfrlem17.o
    dochlss
    syl2anc
    adantr
    wph
    @5
    simpr
    c.pl
    @8
    @2
    cU
    cX
    cY
    lcfrlem17.p
    @12
    lssvacl
    syl21anc
    mtand
    @3
    @4
    ianor
    sylib
end
