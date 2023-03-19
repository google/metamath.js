include "cotp.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "c2nd.mm"
include "wceq.mm"
include "c0g.mm"
include "csn.mm"
include "c1st.mm"
include "csg.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "wne.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simpld.mm"
include "hdmap1cl.mm"
include "eqeltrrd.mm"
include "hdmap1valc.mm"
include "eqtr3d.mm"
include "mapdheq4.mm"
include "eqtrd.mm"

theorem hdmap1eq4N
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vh: setvar h
  let vx: setvar x
  assume hdmap1eq2.h: |- H = ( LHyp ` K )
  assume hdmap1eq2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1eq2.v: |- V = ( Base ` U )
  assume hdmap1eq2.o: |- .0. = ( 0g ` U )
  assume hdmap1eq2.n: |- N = ( LSpan ` U )
  assume hdmap1eq2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1eq2.d: |- D = ( Base ` C )
  assume hdmap1eq2.l: |- L = ( LSpan ` C )
  assume hdmap1eq2.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1eq2.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1eq2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1eq2.f: |- ( ph -> F e. D )
  assume hdmap1eq2.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1eq4.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1eq4.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1eq4.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmap1eq4.ne: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume hdmap1eq4.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1eq4.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume hdmap1eq4.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = B )


  assert |- ( ph -> ( I ` <. Y , G , Z >. ) = B )

  proof
    wph
    cY
    cG
    cZ
    cotp
    #
    cI
    cfv
    @0
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
    cC
    c0g
    cfv
    #
    @2
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
    @1
    c1st
    cfv
    #
    c1st
    cfv
    @2
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
    cC
    csg
    cfv
    #
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
    cfv
    cB
    wph
    vx
    cC
    cD
    @3
    @7
    cU
    vh
    cG
    cH
    cI
    cL
    cK
    @8
    cM
    @6
    cN
    cV
    cW
    cY
    cZ
    c.0
    hdmap1eq2.h
    hdmap1eq2.u
    hdmap1eq2.v
    @6
    eqid
    #
    hdmap1eq2.o
    hdmap1eq2.n
    hdmap1eq2.c
    hdmap1eq2.d
    @7
    eqid
    #
    @3
    eqid
    #
    hdmap1eq2.l
    hdmap1eq2.m
    hdmap1eq2.i
    hdmap1eq2.k
    hdmap1eq4.y
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    cG
    cD
    hdmap1eq4.eg
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1eq2.h
    hdmap1eq2.u
    hdmap1eq2.v
    hdmap1eq2.o
    hdmap1eq2.n
    hdmap1eq2.c
    hdmap1eq2.d
    hdmap1eq2.l
    hdmap1eq2.m
    hdmap1eq2.i
    hdmap1eq2.k
    hdmap1eq2.f
    hdmap1eq2.mn
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
    wne
    @14
    cZ
    csn
    cN
    cfv
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    hdmap1eq2.v
    hdmap1eq2.n
    wph
    cU
    cH
    cK
    cW
    hdmap1eq2.h
    hdmap1eq2.u
    hdmap1eq2.k
    dvhlvec
    wph
    cX
    cV
    c.0
    csn
    #
    hdmap1eq4.x
    eldifad
    wph
    cY
    cV
    @15
    hdmap1eq4.y
    eldifad
    #
    wph
    cZ
    cV
    @15
    hdmap1eq4.z
    eldifad
    #
    hdmap1eq4.xn
    lspindpi
    simpld
    hdmap1eq4.x
    @16
    hdmap1cl
    eqeltrrd
    @17
    @8
    eqid
    #
    hdmap1valc
    wph
    vx
    cC
    cD
    @3
    @7
    cU
    vh
    cB
    cF
    cG
    cH
    @8
    cL
    cK
    cM
    @6
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    @11
    @18
    hdmap1eq2.h
    hdmap1eq2.m
    hdmap1eq2.u
    hdmap1eq2.v
    @9
    hdmap1eq2.o
    hdmap1eq2.n
    hdmap1eq2.c
    hdmap1eq2.d
    @10
    hdmap1eq2.l
    hdmap1eq2.k
    hdmap1eq2.f
    hdmap1eq2.mn
    hdmap1eq4.x
    hdmap1eq4.y
    hdmap1eq4.z
    hdmap1eq4.xn
    hdmap1eq4.ne
    wph
    @13
    @12
    @8
    cfv
    cG
    wph
    vx
    cC
    cD
    @3
    @7
    cU
    vh
    cF
    cH
    cI
    cL
    cK
    @8
    cM
    @6
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1eq2.h
    hdmap1eq2.u
    hdmap1eq2.v
    @9
    hdmap1eq2.o
    hdmap1eq2.n
    hdmap1eq2.c
    hdmap1eq2.d
    @10
    @11
    hdmap1eq2.l
    hdmap1eq2.m
    hdmap1eq2.i
    hdmap1eq2.k
    hdmap1eq4.x
    hdmap1eq2.f
    @16
    @18
    hdmap1valc
    hdmap1eq4.eg
    eqtr3d
    wph
    cX
    cF
    cZ
    cotp
    #
    cI
    cfv
    @19
    @8
    cfv
    cB
    wph
    vx
    cC
    cD
    @3
    @7
    cU
    vh
    cF
    cH
    cI
    cL
    cK
    @8
    cM
    @6
    cN
    cV
    cW
    cX
    cZ
    c.0
    hdmap1eq2.h
    hdmap1eq2.u
    hdmap1eq2.v
    @9
    hdmap1eq2.o
    hdmap1eq2.n
    hdmap1eq2.c
    hdmap1eq2.d
    @10
    @11
    hdmap1eq2.l
    hdmap1eq2.m
    hdmap1eq2.i
    hdmap1eq2.k
    hdmap1eq4.x
    hdmap1eq2.f
    @17
    @18
    hdmap1valc
    hdmap1eq4.ee
    eqtr3d
    mapdheq4
    eqtrd
end
