include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eqidd.mm"
include "hdmapcl.mm"
include "hdmapval2lem.mm"
include "mpbid.mm"
include "eleq1.mm"
include "notbid.mm"
include "oteq1.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "oteq2d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl3c.mm"

theorem hdmapval2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vh: setvar h
  let vz: setvar z
  let cF: class F
  assume hdmapval2.h: |- H = ( LHyp ` K )
  assume hdmapval2.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapval2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapval2.v: |- V = ( Base ` U )
  assume hdmapval2.n: |- N = ( LSpan ` U )
  assume hdmapval2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapval2.d: |- D = ( Base ` C )
  assume hdmapval2.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapval2.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapval2.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapval2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapval2.t: |- ( ph -> T e. V )
  assume hdmapval2.x: |- ( ph -> X e. V )
  assume hdmapval2.ne: |- ( ph -> -. X e. ( ( N ` { E } ) u. ( N ` { T } ) ) )


  assert |- ( ph -> ( S ` T ) = ( I ` <. X , ( I ` <. E , ( J ` E ) , X >. ) , T >. ) )

  proof
    wph
    vz
    cv
    #
    cE
    csn
    cN
    cfv
    cT
    csn
    cN
    cfv
    cun
    #
    wcel
    #
    wn
    #
    cT
    cS
    cfv
    #
    @0
    cE
    cE
    cJ
    cfv
    #
    @0
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    wi
    #
    vz
    cV
    wral
    #
    cX
    cV
    wcel
    cX
    @1
    wcel
    #
    wn
    #
    @4
    cX
    cE
    @5
    cX
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    wph
    @4
    @4
    wceq
    @12
    wph
    @4
    eqidd
    wph
    vz
    cC
    cD
    cS
    cT
    cU
    cE
    @4
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    hdmapval2.h
    hdmapval2.e
    hdmapval2.u
    hdmapval2.v
    hdmapval2.n
    hdmapval2.c
    hdmapval2.d
    hdmapval2.j
    hdmapval2.i
    hdmapval2.s
    hdmapval2.k
    hdmapval2.t
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
    hdmapval2.h
    hdmapval2.u
    hdmapval2.v
    hdmapval2.c
    hdmapval2.d
    hdmapval2.s
    hdmapval2.k
    hdmapval2.t
    hdmapcl
    hdmapval2lem
    mpbid
    hdmapval2.x
    hdmapval2.ne
    @11
    @14
    @19
    wi
    vz
    cX
    cV
    @0
    cX
    wceq
    #
    @3
    @14
    @10
    @19
    @20
    @2
    @13
    @0
    cX
    @1
    eleq1
    notbid
    @20
    @9
    @18
    @4
    @20
    @8
    @17
    cI
    @20
    @8
    cX
    @7
    cT
    cotp
    @17
    @0
    cX
    @7
    cT
    oteq1
    @20
    @7
    @16
    cX
    cT
    @20
    @6
    @15
    cI
    @0
    cX
    cE
    @5
    oteq3
    fveq2d
    oteq2d
    eqtrd
    fveq2d
    eqeq2d
    imbi12d
    rspccv
    syl3c
end
