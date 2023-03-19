include "co.mm"
include "cop.mm"
include "cfv.mm"
include "cmpt.mm"
include "cflf.mm"
include "df-ov.mm"
include "ccom.mm"
include "ctx.mm"
include "cxp.mm"
include "ctopon.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "ccnp.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "opelxpi.mm"
include "eqid.mm"
include "fmptd.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfop.mm"
include "wceq.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "cbvmpt.mm"
include "txflf.mm"
include "mpbir2and.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "flfcnp.mm"
include "syl32anc.mm"
include "eqidd.mm"
include "cuni.mm"
include "ctop.mm"
include "cnptop2.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "syl6eqr.mm"
include "fmptco.mm"
include "syl5eqel.mm"

theorem flfcnp2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  assume flfcnp2.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume flfcnp2.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume flfcnp2.l: |- ( ph -> L e. ( Fil ` Z ) )
  assume flfcnp2.a: |- ( ( ph /\ x e. Z ) -> A e. X )
  assume flfcnp2.b: |- ( ( ph /\ x e. Z ) -> B e. Y )
  assume flfcnp2.r: |- ( ph -> R e. ( ( J fLimf L ) ` ( x e. Z |-> A ) ) )
  assume flfcnp2.s: |- ( ph -> S e. ( ( K fLimf L ) ` ( x e. Z |-> B ) ) )
  assume flfcnp2.o: |- ( ph -> O e. ( ( ( J tX K ) CnP N ) ` <. R , S >. ) )

  disjoint O x
  disjoint ph x
  disjoint Z x
  disjoint X x
  disjoint Y x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint O y
  disjoint ph y
  disjoint Z y
  disjoint X y
  disjoint Y y
  assert |- ( ph -> ( R O S ) e. ( ( N fLimf L ) ` ( x e. Z |-> ( A O B ) ) ) )

  proof
    wph
    cR
    cS
    cO
    co
    cR
    cS
    cop
    #
    cO
    cfv
    #
    vx
    cZ
    cA
    cB
    cO
    co
    #
    cmpt
    #
    cN
    cL
    cflf
    co
    #
    cfv
    #
    cR
    cS
    cO
    df-ov
    wph
    @1
    cO
    vx
    cZ
    cA
    cB
    cop
    #
    cmpt
    #
    ccom
    #
    @4
    cfv
    #
    @5
    wph
    cJ
    cK
    ctx
    co
    #
    cX
    cY
    cxp
    #
    ctopon
    cfv
    wcel
    #
    cL
    cZ
    cfil
    cfv
    wcel
    cZ
    @11
    @7
    wf
    @0
    @7
    @10
    cL
    cflf
    co
    #
    cfv
    #
    wcel
    cO
    @0
    @10
    cN
    ccnp
    co
    cfv
    wcel
    #
    @1
    @9
    wcel
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
    @12
    flfcnp2.j
    flfcnp2.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    #
    flfcnp2.l
    wph
    vx
    cZ
    @6
    @11
    @7
    wph
    vx
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    @6
    @11
    wcel
    flfcnp2.a
    flfcnp2.b
    cA
    cB
    cX
    cY
    opelxpi
    syl2anc
    #
    @7
    eqid
    fmptd
    wph
    @0
    vx
    cZ
    @17
    vx
    cZ
    cA
    cmpt
    #
    cfv
    #
    @17
    vx
    cZ
    cB
    cmpt
    #
    cfv
    #
    cop
    #
    cmpt
    #
    @13
    cfv
    #
    @14
    wph
    @0
    @29
    wcel
    cR
    @23
    cJ
    cL
    cflf
    co
    cfv
    wcel
    cS
    @25
    cK
    cL
    cflf
    co
    cfv
    wcel
    flfcnp2.r
    flfcnp2.s
    wph
    cR
    cS
    vy
    @23
    @25
    @28
    cJ
    cK
    cL
    cX
    cY
    cZ
    flfcnp2.j
    flfcnp2.k
    flfcnp2.l
    wph
    vx
    cZ
    cA
    cX
    @23
    flfcnp2.a
    @23
    eqid
    #
    fmptd
    wph
    vx
    cZ
    cB
    cY
    @25
    flfcnp2.b
    @25
    eqid
    #
    fmptd
    vx
    vy
    cZ
    @27
    vy
    cv
    #
    @23
    cfv
    #
    @32
    @25
    cfv
    #
    cop
    vy
    @27
    nfcv
    vx
    @33
    @34
    vx
    cZ
    cA
    @32
    nffvmpt1
    vx
    cZ
    cB
    @32
    nffvmpt1
    nfop
    @17
    @32
    wceq
    @24
    @33
    @26
    @34
    @17
    @32
    @23
    fveq2
    @17
    @32
    @25
    fveq2
    opeq12d
    cbvmpt
    txflf
    mpbir2and
    wph
    @28
    @7
    @13
    wph
    vx
    cZ
    @27
    @6
    @19
    @24
    cA
    @26
    cB
    @19
    @18
    @20
    @24
    cA
    wceq
    wph
    @18
    simpr
    #
    flfcnp2.a
    vx
    cZ
    cA
    cX
    @23
    @30
    fvmpt2
    syl2anc
    @19
    @18
    @21
    @26
    cB
    wceq
    @35
    flfcnp2.b
    vx
    cZ
    cB
    cY
    @25
    @31
    fvmpt2
    syl2anc
    opeq12d
    mpteq2dva
    fveq2d
    eleqtrd
    flfcnp2.o
    @0
    @7
    cO
    @10
    cN
    cL
    @11
    cZ
    flfcnp
    syl32anc
    wph
    @8
    @3
    @4
    wph
    vx
    vy
    cZ
    @11
    @6
    @32
    cO
    cfv
    #
    @2
    @7
    cO
    @22
    wph
    @7
    eqidd
    wph
    vy
    @11
    cN
    cuni
    #
    cO
    wph
    @12
    cN
    @37
    ctopon
    cfv
    wcel
    #
    @15
    @11
    @37
    cO
    wf
    @16
    wph
    cN
    ctop
    wcel
    #
    @38
    wph
    @15
    @39
    flfcnp2.o
    @0
    cO
    @10
    cN
    cnptop2
    syl
    cN
    @37
    @37
    eqid
    toptopon
    sylib
    flfcnp2.o
    @0
    cO
    @10
    cN
    @11
    @37
    cnpf2
    syl3anc
    feqmptd
    @32
    @6
    wceq
    @36
    @6
    cO
    cfv
    @2
    @32
    @6
    cO
    fveq2
    cA
    cB
    cO
    df-ov
    syl6eqr
    fmptco
    fveq2d
    eleqtrd
    syl5eqel
end
