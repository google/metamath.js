include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifad.mm"
include "hdmapcl.mm"
include "eldifsni.mm"
include "syl.mm"
include "hdmapeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem hdmapnzcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume hdmapnzcl.h: |- H = ( LHyp ` K )
  assume hdmapnzcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapnzcl.v: |- V = ( Base ` U )
  assume hdmapnzcl.o: |- .0. = ( 0g ` U )
  assume hdmapnzcl.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapnzcl.q: |- Q = ( 0g ` C )
  assume hdmapnzcl.d: |- D = ( Base ` C )
  assume hdmapnzcl.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapnzcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapnzcl.t: |- ( ph -> T e. ( V \ { .0. } ) )


  assert |- ( ph -> ( S ` T ) e. ( D \ { Q } ) )

  proof
    wph
    cT
    cS
    cfv
    #
    cD
    wcel
    @0
    cQ
    wne
    #
    @0
    cD
    cQ
    csn
    cdif
    wcel
    wph
    cC
    cD
    cS
    cT
    cU
    cH
    cK
    cV
    cW
    hdmapnzcl.h
    hdmapnzcl.u
    hdmapnzcl.v
    hdmapnzcl.c
    hdmapnzcl.d
    hdmapnzcl.s
    hdmapnzcl.k
    wph
    cT
    cV
    c.0
    csn
    #
    hdmapnzcl.t
    eldifad
    #
    hdmapcl
    wph
    @1
    cT
    c.0
    wne
    #
    wph
    cT
    cV
    @2
    cdif
    wcel
    @4
    hdmapnzcl.t
    cT
    cV
    c.0
    eldifsni
    syl
    wph
    @0
    cQ
    cT
    c.0
    wph
    cC
    cQ
    cS
    cT
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmapnzcl.h
    hdmapnzcl.u
    hdmapnzcl.v
    hdmapnzcl.o
    hdmapnzcl.c
    hdmapnzcl.q
    hdmapnzcl.s
    hdmapnzcl.k
    @3
    hdmapeq0
    necon3bid
    mpbird
    @0
    cD
    cQ
    eldifsn
    sylanbrc
end
