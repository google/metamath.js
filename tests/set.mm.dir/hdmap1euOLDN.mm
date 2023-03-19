include "c0g.mm"
include "cfv.mm"
include "csg.mm"
include "cvv.mm"
include "cv.mm"
include "c2nd.mm"
include "wceq.mm"
include "csn.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "hdmap1cbv.mm"
include "hdmap1eulemOLDN.mm"

theorem hdmap1euOLDN
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  assume hdmap1eu.h: |- H = ( LHyp ` K )
  assume hdmap1eu.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1eu.v: |- V = ( Base ` U )
  assume hdmap1eu.o: |- .0. = ( 0g ` U )
  assume hdmap1eu.n: |- N = ( LSpan ` U )
  assume hdmap1eu.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1eu.d: |- D = ( Base ` C )
  assume hdmap1eu.l: |- L = ( LSpan ` C )
  assume hdmap1eu.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1eu.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1eu.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1eu.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1eu.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1eu.f: |- ( ph -> F e. D )
  assume hdmap1eu.t: |- ( ph -> T e. V )

  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint L y
  disjoint L z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint .0. y
  disjoint .0. z
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint ph z
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint C h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint D g
  disjoint D h
  disjoint D w
  disjoint D x
  disjoint F g
  disjoint F w
  disjoint L g
  disjoint L h
  disjoint L w
  disjoint L x
  disjoint M g
  disjoint M h
  disjoint M w
  disjoint M x
  disjoint N g
  disjoint N h
  disjoint N w
  disjoint N x
  disjoint .0. g
  disjoint .0. w
  disjoint .0. x
  disjoint T g
  disjoint T w
  disjoint U g
  disjoint U h
  disjoint U w
  disjoint U x
  disjoint V g
  disjoint X g
  disjoint X w
  disjoint g ph
  assert |- ( ph -> E! y e. D A. z e. V ( -. z e. ( N ` { X , T } ) -> y = ( I ` <. z , ( I ` <. X , F , z >. ) , T >. ) ) )

  proof
    wph
    vw
    vy
    vz
    cC
    cD
    cC
    c0g
    cfv
    #
    cC
    csg
    cfv
    #
    cT
    cU
    vg
    cF
    cH
    cI
    cL
    cK
    vx
    cvv
    vx
    cv
    #
    c2nd
    cfv
    #
    c.0
    wceq
    @0
    @3
    csn
    cN
    cfv
    cM
    cfv
    vh
    cv
    #
    csn
    cL
    cfv
    wceq
    @2
    c1st
    cfv
    #
    c1st
    cfv
    @3
    cU
    csg
    cfv
    #
    co
    csn
    cN
    cfv
    cM
    cfv
    @5
    c2nd
    cfv
    @4
    @1
    co
    csn
    cL
    cfv
    wceq
    wa
    vh
    cD
    crio
    cif
    cmpt
    #
    cM
    @6
    cN
    cV
    cW
    cX
    c.0
    hdmap1eu.h
    hdmap1eu.u
    hdmap1eu.v
    @6
    eqid
    hdmap1eu.o
    hdmap1eu.n
    hdmap1eu.c
    hdmap1eu.d
    @1
    eqid
    @0
    eqid
    hdmap1eu.l
    hdmap1eu.m
    hdmap1eu.i
    hdmap1eu.k
    hdmap1eu.mn
    hdmap1eu.x
    hdmap1eu.f
    hdmap1eu.t
    vx
    vw
    cD
    @0
    @1
    vh
    vg
    cL
    @7
    cM
    @6
    cN
    c.0
    @7
    eqid
    hdmap1cbv
    hdmap1eulemOLDN
end
