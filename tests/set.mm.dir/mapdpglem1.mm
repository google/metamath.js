include "co.mm"
include "csn.mm"
include "cfv.mm"
include "clsm.mm"
include "wss.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lspsntrim.mm"
include "syl3anc.mm"
include "clss.mm"
include "lmodvsubcl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "mapdord.mm"
include "mpbird.mm"
include "mapdlsm.mm"
include "sseqtrd.mm"

theorem mapdpglem1
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdpglem.h: |- H = ( LHyp ` K )
  assume mapdpglem.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdpglem.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdpglem.v: |- V = ( Base ` U )
  assume mapdpglem.s: |- .- = ( -g ` U )
  assume mapdpglem.n: |- N = ( LSpan ` U )
  assume mapdpglem.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdpglem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdpglem.x: |- ( ph -> X e. V )
  assume mapdpglem.y: |- ( ph -> Y e. V )
  assume mapdpglem1.p: |- .(+) = ( LSSum ` C )


  assert |- ( ph -> ( M ` ( N ` { ( X .- Y ) } ) ) C_ ( ( M ` ( N ` { X } ) ) .(+) ( M ` ( N ` { Y } ) ) ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
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
    cM
    cfv
    #
    @3
    cM
    cfv
    @4
    cM
    cfv
    c.po
    co
    wph
    @2
    @7
    wss
    @1
    @6
    wss
    #
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @8
    wph
    cU
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem.k
    dvhlmod
    #
    mapdpglem.x
    mapdpglem.y
    @5
    c.mi
    cN
    cV
    cU
    cX
    cY
    mapdpglem.v
    mapdpglem.s
    @5
    eqid
    #
    mapdpglem.n
    lspsntrim
    syl3anc
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @1
    @6
    mapdpglem.h
    mapdpglem.u
    @14
    eqid
    #
    mapdpglem.m
    mapdpglem.k
    wph
    @9
    @0
    cV
    wcel
    #
    @1
    @14
    wcel
    @12
    wph
    @9
    @10
    @11
    @16
    @12
    mapdpglem.x
    mapdpglem.y
    c.mi
    cV
    cU
    cX
    cY
    mapdpglem.v
    mapdpglem.s
    lmodvsubcl
    syl3anc
    @14
    cN
    cV
    cU
    @0
    mapdpglem.v
    @15
    mapdpglem.n
    lspsncl
    syl2anc
    wph
    @9
    @3
    @14
    wcel
    #
    @4
    @14
    wcel
    #
    @6
    @14
    wcel
    @12
    wph
    @9
    @10
    @17
    @12
    mapdpglem.x
    @14
    cN
    cV
    cU
    cX
    mapdpglem.v
    @15
    mapdpglem.n
    lspsncl
    syl2anc
    #
    wph
    @9
    @11
    @18
    @12
    mapdpglem.y
    @14
    cN
    cV
    cU
    cY
    mapdpglem.v
    @15
    mapdpglem.n
    lspsncl
    syl2anc
    #
    @5
    @14
    @3
    @4
    cU
    @15
    @13
    lsmcl
    syl3anc
    mapdord
    mpbird
    wph
    cC
    c.po
    @5
    @14
    cU
    cH
    cK
    cM
    cW
    @3
    @4
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @15
    @13
    mapdpglem.c
    mapdpglem1.p
    mapdpglem.k
    @19
    @20
    mapdlsm
    sseqtrd
end
