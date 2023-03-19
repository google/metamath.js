include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cpr.mm"
include "cin.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "cdif.mm"
include "wne.mm"
include "simpr.mm"
include "lcfrlem20.mm"
include "clmod.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodcom.mm"
include "syl3anc.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimprd.mm"
include "con3dimp.mm"
include "prcom.mm"
include "fveq2i.mm"
include "a1i.mm"
include "ineq12d.mm"
include "necomd.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "lcfrlem19.mm"
include "mpjaodan.mm"

theorem lcfrlem21
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


  assert |- ( ph -> ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) ) e. A )

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
    wn
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @2
    cin
    #
    cA
    wcel
    #
    cY
    @2
    wcel
    #
    wn
    #
    wph
    @3
    wa
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @3
    lcfrlem17.k
    adantr
    wph
    cX
    cV
    c.0
    csn
    #
    cdif
    #
    wcel
    #
    @3
    lcfrlem17.x
    adantr
    wph
    cY
    @12
    wcel
    #
    @3
    lcfrlem17.y
    adantr
    wph
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
    wne
    @3
    lcfrlem17.ne
    adantr
    wph
    @3
    simpr
    lcfrlem20
    wph
    @9
    cY
    cY
    cX
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
    wn
    #
    @7
    wph
    @20
    @8
    wph
    @8
    @20
    wph
    @2
    @19
    cY
    wph
    @1
    @18
    c.pe
    wph
    @0
    @17
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
    @0
    @17
    wceq
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    wph
    cX
    cV
    @11
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
    lmodcom
    syl3anc
    sneqd
    fveq2d
    #
    eleq2d
    biimprd
    con3dimp
    wph
    @21
    wa
    #
    @6
    cY
    cX
    cpr
    #
    cN
    cfv
    #
    @19
    cin
    #
    cA
    wph
    @6
    @26
    wceq
    @21
    wph
    @5
    @25
    @2
    @19
    @5
    @25
    wceq
    wph
    @4
    @24
    cN
    cX
    cY
    prcom
    fveq2i
    a1i
    @22
    ineq12d
    adantr
    @23
    cA
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cY
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    wph
    @10
    @21
    lcfrlem17.k
    adantr
    wph
    @14
    @21
    lcfrlem17.y
    adantr
    wph
    @13
    @21
    lcfrlem17.x
    adantr
    wph
    @16
    @15
    wne
    @21
    wph
    @15
    @16
    lcfrlem17.ne
    necomd
    adantr
    wph
    @21
    simpr
    lcfrlem20
    eqeltrd
    syldan
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
    lcfrlem19
    mpjaodan
end
