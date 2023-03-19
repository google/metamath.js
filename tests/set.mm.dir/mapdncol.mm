include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "3netr3d.mm"

theorem mapdncol
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdindp.h: |- H = ( LHyp ` K )
  assume mapdindp.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdindp.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdindp.v: |- V = ( Base ` U )
  assume mapdindp.n: |- N = ( LSpan ` U )
  assume mapdindp.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdindp.d: |- D = ( Base ` C )
  assume mapdindp.j: |- J = ( LSpan ` C )
  assume mapdindp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdindp.f: |- ( ph -> F e. D )
  assume mapdindp.mx: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdindp.x: |- ( ph -> X e. V )
  assume mapdindp.y: |- ( ph -> Y e. V )
  assume mapdindp.g: |- ( ph -> G e. D )
  assume mapdindp.my: |- ( ph -> ( M ` ( N ` { Y } ) ) = ( J ` { G } ) )
  assume mapdncol.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( J ` { F } ) =/= ( J ` { G } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cF
    csn
    cJ
    cfv
    cG
    csn
    cJ
    cfv
    wph
    @1
    @3
    wne
    @0
    @2
    wne
    mapdncol.q
    wph
    @1
    @3
    @0
    @2
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
    @0
    @2
    mapdindp.h
    mapdindp.u
    @4
    eqid
    #
    mapdindp.m
    mapdindp.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    @0
    @4
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdindp.h
    mapdindp.u
    mapdindp.k
    dvhlmod
    #
    mapdindp.x
    @4
    cN
    cV
    cU
    cX
    mapdindp.v
    @5
    mapdindp.n
    lspsncl
    syl2anc
    wph
    @6
    cY
    cV
    wcel
    @2
    @4
    wcel
    @7
    mapdindp.y
    @4
    cN
    cV
    cU
    cY
    mapdindp.v
    @5
    mapdindp.n
    lspsncl
    syl2anc
    mapd11
    necon3bid
    mpbird
    mapdindp.mx
    mapdindp.my
    3netr3d
end
