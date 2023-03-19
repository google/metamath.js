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
include "hdmap1valc.mm"
include "mapdhcl.mm"
include "eqeltrd.mm"

theorem hdmap1cl
  let wph: wff ph
  let cC: class C
  let cD: class D
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
  let cY: class Y
  let c.0: class .0.
  let vh: setvar h
  let vx: setvar x
  let cG: class G
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
  assume hdmap1cl.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume hdmap1cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1cl.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( I ` <. X , F , Y >. ) e. D )

  proof
    wph
    cX
    cF
    cY
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
    cD
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
    hdmap1cl.x
    hdmap1eq2.f
    hdmap1cl.y
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
    cF
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
    @11
    @12
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
    hdmap1cl.x
    hdmap1cl.y
    hdmap1cl.ne
    mapdhcl
    eqeltrd
end
