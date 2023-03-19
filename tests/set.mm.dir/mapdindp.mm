include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "dvhlmod.mm"
include "clmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdord.mm"
include "clsm.mm"
include "co.mm"
include "lsmpr.mm"
include "fveq2d.mm"
include "mapdlsm.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "sseq12d.mm"
include "3bitr2rd.mm"
include "bitrd.mm"
include "mtbird.mm"

theorem mapdindp
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cE: class E
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
  let cZ: class Z
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
  assume mapdindp.z: |- ( ph -> Z e. V )
  assume mapdindp.e: |- ( ph -> E e. D )
  assume mapdindp.mg: |- ( ph -> ( M ` ( N ` { Z } ) ) = ( J ` { E } ) )
  assume mapdindp.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )


  assert |- ( ph -> -. F e. ( J ` { G , E } ) )

  proof
    wph
    cF
    cG
    cE
    cpr
    cJ
    cfv
    #
    wcel
    #
    cX
    cY
    cZ
    cpr
    cN
    cfv
    #
    wcel
    #
    mapdindp.xn
    wph
    @1
    cF
    csn
    cJ
    cfv
    #
    @0
    wss
    #
    @3
    wph
    cC
    clss
    cfv
    #
    @0
    cJ
    cD
    cC
    cF
    mapdindp.d
    @6
    eqid
    #
    mapdindp.j
    wph
    cC
    cH
    cK
    cW
    mapdindp.h
    mapdindp.c
    mapdindp.k
    lcdlmod
    #
    wph
    @6
    cJ
    cD
    cC
    cG
    cE
    mapdindp.d
    @7
    mapdindp.j
    @8
    mapdindp.g
    mapdindp.e
    lspprcl
    mapdindp.f
    lspsnel5
    wph
    @3
    cX
    csn
    cN
    cfv
    #
    @2
    wss
    @9
    cM
    cfv
    #
    @2
    cM
    cfv
    #
    wss
    @5
    wph
    cU
    clss
    cfv
    #
    @2
    cN
    cV
    cU
    cX
    mapdindp.v
    @12
    eqid
    #
    mapdindp.n
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
    wph
    @12
    cN
    cV
    cU
    cY
    cZ
    mapdindp.v
    @13
    mapdindp.n
    @14
    mapdindp.y
    mapdindp.z
    lspprcl
    #
    mapdindp.x
    lspsnel5
    wph
    @12
    cU
    cH
    cK
    cM
    cW
    @9
    @2
    mapdindp.h
    mapdindp.u
    @13
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
    @9
    @12
    wcel
    @14
    mapdindp.x
    @12
    cN
    cV
    cU
    cX
    mapdindp.v
    @13
    mapdindp.n
    lspsncl
    syl2anc
    @15
    mapdord
    wph
    @10
    @4
    @11
    @0
    mapdindp.mx
    wph
    @11
    cG
    csn
    cJ
    cfv
    #
    cE
    csn
    cJ
    cfv
    #
    cC
    clsm
    cfv
    #
    co
    #
    @0
    wph
    @11
    cY
    csn
    cN
    cfv
    #
    cZ
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
    @21
    cM
    cfv
    #
    @22
    cM
    cfv
    #
    @19
    co
    @20
    wph
    @2
    @24
    cM
    wph
    @23
    cN
    cV
    cU
    cY
    cZ
    mapdindp.v
    mapdindp.n
    @23
    eqid
    #
    @14
    mapdindp.y
    mapdindp.z
    lsmpr
    fveq2d
    wph
    cC
    @19
    @23
    @12
    cU
    cH
    cK
    cM
    cW
    @21
    @22
    mapdindp.h
    mapdindp.m
    mapdindp.u
    @13
    @27
    mapdindp.c
    @19
    eqid
    #
    mapdindp.k
    wph
    @16
    cY
    cV
    wcel
    @21
    @12
    wcel
    @14
    mapdindp.y
    @12
    cN
    cV
    cU
    cY
    mapdindp.v
    @13
    mapdindp.n
    lspsncl
    syl2anc
    wph
    @16
    cZ
    cV
    wcel
    @22
    @12
    wcel
    @14
    mapdindp.z
    @12
    cN
    cV
    cU
    cZ
    mapdindp.v
    @13
    mapdindp.n
    lspsncl
    syl2anc
    mapdlsm
    wph
    @25
    @17
    @26
    @18
    @19
    mapdindp.my
    mapdindp.mg
    oveq12d
    3eqtrd
    wph
    @19
    cJ
    cD
    cC
    cG
    cE
    mapdindp.d
    mapdindp.j
    @28
    @8
    mapdindp.g
    mapdindp.e
    lsmpr
    eqtr4d
    sseq12d
    3bitr2rd
    bitrd
    mtbird
end
