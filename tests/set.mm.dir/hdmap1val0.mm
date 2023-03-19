include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "clspn.mm"
include "cmpd.mm"
include "cv.mm"
include "csg.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "chlt.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "hdmap1val.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem hdmap1val0
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vh: setvar h
  assume hdmap1val0.h: |- H = ( LHyp ` K )
  assume hdmap1val0.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1val0.v: |- V = ( Base ` U )
  assume hdmap1val0.o: |- .0. = ( 0g ` U )
  assume hdmap1val0.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1val0.d: |- D = ( Base ` C )
  assume hdmap1val0.q: |- Q = ( 0g ` C )
  assume hdmap1val0.s: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1val0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1val0.f: |- ( ph -> F e. D )
  assume hdmap1val0.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( I ` <. X , F , .0. >. ) = Q )

  proof
    wph
    cX
    cF
    c.0
    cotp
    cI
    cfv
    c.0
    c.0
    wceq
    #
    cQ
    c.0
    csn
    cU
    clspn
    cfv
    #
    cfv
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cfv
    vh
    cv
    #
    csn
    cC
    clspn
    cfv
    #
    cfv
    wceq
    cX
    c.0
    cU
    csg
    cfv
    #
    co
    csn
    @1
    cfv
    @2
    cfv
    cF
    @3
    cC
    csg
    cfv
    #
    co
    csn
    @4
    cfv
    wceq
    wa
    vh
    cD
    crio
    #
    cif
    cQ
    wph
    chlt
    cC
    cD
    cQ
    @6
    cU
    vh
    cF
    cH
    cI
    @4
    cK
    @2
    @5
    @1
    cV
    cW
    cX
    c.0
    c.0
    hdmap1val0.h
    hdmap1val0.u
    hdmap1val0.v
    @5
    eqid
    hdmap1val0.o
    @1
    eqid
    hdmap1val0.c
    hdmap1val0.d
    @6
    eqid
    hdmap1val0.q
    @4
    eqid
    @2
    eqid
    hdmap1val0.s
    hdmap1val0.k
    hdmap1val0.x
    hdmap1val0.f
    wph
    cU
    clmod
    wcel
    c.0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap1val0.h
    hdmap1val0.u
    hdmap1val0.k
    dvhlmod
    cV
    cU
    c.0
    hdmap1val0.v
    hdmap1val0.o
    lmod0vcl
    syl
    hdmap1val
    @0
    cQ
    @7
    c.0
    eqid
    iftruei
    syl6eq
end
