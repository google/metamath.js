include "cop.mm"
include "cfv.mm"
include "co.mm"
include "clm.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "cuni.mm"
include "ctx.mm"
include "ctopon.mm"
include "ccn.mm"
include "wf.mm"
include "txtopon.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "fmptco.mm"
include "wbr.mm"
include "txlm.mm"
include "mpbi2and.mm"
include "lmcn.mm"
include "eqbrtrrd.mm"
include "syl6breqr.mm"

theorem lmcn2
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vt: setvar t
  assume txlm.z: |- Z = ( ZZ>= ` M )
  assume txlm.m: |- ( ph -> M e. ZZ )
  assume txlm.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume txlm.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txlm.f: |- ( ph -> F : Z --> X )
  assume txlm.g: |- ( ph -> G : Z --> Y )
  assume lmcn2.fl: |- ( ph -> F ( ~~>t ` J ) R )
  assume lmcn2.gl: |- ( ph -> G ( ~~>t ` K ) S )
  assume lmcn2.o: |- ( ph -> O e. ( ( J tX K ) Cn N ) )
  assume lmcn2.h: |- H = ( n e. Z |-> ( ( F ` n ) O ( G ` n ) ) )

  disjoint F n
  disjoint O n
  disjoint n ph
  disjoint G n
  disjoint J n
  disjoint K n
  disjoint X n
  disjoint Y n
  disjoint Z n
  disjoint j k
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint F j
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint F k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint F v
  disjoint w x
  disjoint F w
  disjoint F x
  disjoint H j
  disjoint H k
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint O x
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint G j
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint M j
  disjoint M k
  disjoint j t
  disjoint R j
  disjoint k t
  disjoint R k
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint S j
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint J j
  disjoint J k
  disjoint n t
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint K j
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Z j
  disjoint Z k
  disjoint Z u
  disjoint Z v
  disjoint Z w
  assert |- ( ph -> H ( ~~>t ` N ) ( R O S ) )

  proof
    wph
    cH
    cR
    cS
    cop
    #
    cO
    cfv
    #
    cR
    cS
    cO
    co
    cN
    clm
    cfv
    #
    wph
    cO
    vn
    cZ
    vn
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cop
    #
    cmpt
    #
    ccom
    #
    cH
    @1
    @2
    wph
    @8
    vn
    cZ
    @4
    @5
    cO
    co
    #
    cmpt
    cH
    wph
    vn
    vx
    cZ
    cX
    cY
    cxp
    #
    @6
    vx
    cv
    #
    cO
    cfv
    #
    @9
    @7
    cO
    wph
    @3
    cZ
    wcel
    wa
    @4
    cX
    wcel
    @5
    cY
    wcel
    @6
    @10
    wcel
    wph
    cZ
    cX
    @3
    cF
    txlm.f
    ffvelrnda
    wph
    cZ
    cY
    @3
    cG
    txlm.g
    ffvelrnda
    @4
    @5
    cX
    cY
    opelxpi
    syl2anc
    wph
    @7
    eqidd
    wph
    vx
    @10
    cN
    cuni
    #
    cO
    wph
    cJ
    cK
    ctx
    co
    #
    @10
    ctopon
    cfv
    wcel
    #
    cN
    @13
    ctopon
    cfv
    wcel
    #
    cO
    @14
    cN
    ccn
    co
    wcel
    #
    @10
    @13
    cO
    wf
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @15
    txlm.j
    txlm.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    wph
    cN
    ctop
    wcel
    #
    @16
    wph
    @17
    @18
    lmcn2.o
    cO
    @14
    cN
    cntop2
    syl
    cN
    @13
    @13
    eqid
    toptopon
    sylib
    lmcn2.o
    cO
    @14
    cN
    @10
    @13
    cnf2
    syl3anc
    feqmptd
    @11
    @6
    wceq
    @12
    @6
    cO
    cfv
    @9
    @11
    @6
    cO
    fveq2
    @4
    @5
    cO
    df-ov
    syl6eqr
    fmptco
    lmcn2.h
    syl6eqr
    wph
    @0
    @7
    cO
    @14
    cN
    wph
    cF
    cR
    cJ
    clm
    cfv
    wbr
    cG
    cS
    cK
    clm
    cfv
    wbr
    @7
    @0
    @14
    clm
    cfv
    wbr
    lmcn2.fl
    lmcn2.gl
    wph
    cR
    cS
    vn
    cF
    cG
    @7
    cJ
    cK
    cM
    cX
    cY
    cZ
    txlm.z
    txlm.m
    txlm.j
    txlm.k
    txlm.f
    txlm.g
    @7
    eqid
    txlm
    mpbi2and
    lmcn2.o
    lmcn
    eqbrtrrd
    cR
    cS
    cO
    df-ov
    syl6breqr
end
