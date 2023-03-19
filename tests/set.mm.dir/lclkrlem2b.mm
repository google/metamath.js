include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "co.mm"
include "cin.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "cdif.mm"
include "wne.mm"
include "simpr.mm"
include "lclkrlem2a.mm"
include "wceq.mm"
include "cabl.mm"
include "csubg.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "necomd.mm"
include "eqeltrd.mm"
include "mpjaodan.mm"

theorem lclkrlem2b
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.po: class .(+)
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
  assume lclkrlem2a.h: |- H = ( LHyp ` K )
  assume lclkrlem2a.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2a.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2a.v: |- V = ( Base ` U )
  assume lclkrlem2a.z: |- .0. = ( 0g ` U )
  assume lclkrlem2a.p: |- .(+) = ( LSSum ` U )
  assume lclkrlem2a.n: |- N = ( LSpan ` U )
  assume lclkrlem2a.a: |- A = ( LSAtoms ` U )
  assume lclkrlem2a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2a.b: |- ( ph -> B e. ( V \ { .0. } ) )
  assume lclkrlem2a.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2a.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lclkrlem2a.e: |- ( ph -> ( ._|_ ` { X } ) =/= ( ._|_ ` { Y } ) )
  assume lclkrlem2b.da: |- ( ph -> ( -. X e. ( ._|_ ` { B } ) \/ -. Y e. ( ._|_ ` { B } ) ) )


  assert |- ( ph -> ( ( ( N ` { X } ) .(+) ( N ` { Y } ) ) i^i ( ._|_ ` { B } ) ) e. A )

  proof
    wph
    cX
    cB
    csn
    c.pe
    cfv
    #
    wcel
    wn
    #
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    c.po
    co
    #
    @0
    cin
    #
    cA
    wcel
    cY
    @0
    wcel
    wn
    #
    wph
    @1
    wa
    cA
    cB
    c.po
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
    lclkrlem2a.h
    lclkrlem2a.o
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.z
    lclkrlem2a.p
    lclkrlem2a.n
    lclkrlem2a.a
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
    lclkrlem2a.k
    adantr
    wph
    cB
    cV
    c.0
    csn
    #
    cdif
    #
    wcel
    #
    @1
    lclkrlem2a.b
    adantr
    wph
    cX
    @11
    wcel
    #
    @1
    lclkrlem2a.x
    adantr
    wph
    cY
    @11
    wcel
    #
    @1
    lclkrlem2a.y
    adantr
    wph
    @2
    c.pe
    cfv
    #
    @4
    c.pe
    cfv
    #
    wne
    @1
    lclkrlem2a.e
    adantr
    wph
    @1
    simpr
    lclkrlem2a
    wph
    @8
    wa
    #
    @7
    @5
    @3
    c.po
    co
    #
    @0
    cin
    #
    cA
    wph
    @7
    @19
    wceq
    @8
    wph
    @6
    @18
    @0
    wph
    cU
    cabl
    wcel
    #
    @3
    cU
    csubg
    cfv
    #
    wcel
    @5
    @21
    wcel
    @6
    @18
    wceq
    wph
    cU
    clmod
    wcel
    #
    @20
    wph
    cU
    cH
    cK
    cW
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.k
    dvhlmod
    #
    cU
    lmodabl
    syl
    wph
    cU
    clss
    cfv
    #
    @21
    @3
    wph
    @22
    @24
    @21
    wss
    @23
    @24
    cU
    @24
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @22
    cX
    cV
    wcel
    @3
    @24
    wcel
    @23
    wph
    cX
    cV
    @10
    lclkrlem2a.x
    eldifad
    @24
    cN
    cV
    cU
    cX
    lclkrlem2a.v
    @25
    lclkrlem2a.n
    lspsncl
    syl2anc
    sseldd
    wph
    @24
    @21
    @5
    @26
    wph
    @22
    cY
    cV
    wcel
    @5
    @24
    wcel
    @23
    wph
    cY
    cV
    @10
    lclkrlem2a.y
    eldifad
    @24
    cN
    cV
    cU
    cY
    lclkrlem2a.v
    @25
    lclkrlem2a.n
    lspsncl
    syl2anc
    sseldd
    c.po
    @3
    @5
    cU
    lclkrlem2a.p
    lsmcom
    syl3anc
    ineq1d
    adantr
    @17
    cA
    cB
    c.po
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
    lclkrlem2a.h
    lclkrlem2a.o
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.z
    lclkrlem2a.p
    lclkrlem2a.n
    lclkrlem2a.a
    wph
    @9
    @8
    lclkrlem2a.k
    adantr
    wph
    @12
    @8
    lclkrlem2a.b
    adantr
    wph
    @14
    @8
    lclkrlem2a.y
    adantr
    wph
    @13
    @8
    lclkrlem2a.x
    adantr
    wph
    @16
    @15
    wne
    @8
    wph
    @15
    @16
    lclkrlem2a.e
    necomd
    adantr
    wph
    @8
    simpr
    lclkrlem2a
    eqeltrd
    lclkrlem2b.da
    mpjaodan
end
