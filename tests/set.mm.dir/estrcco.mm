include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "estrccofval.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "adantl.mm"
include "simprl.mm"
include "fveq2d.mm"
include "wcel.mm"
include "op2ndg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "op1stg.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "opelxpi.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "simpl.mm"
include "simpr.mm"
include "coeq12d.mm"
include "wf.mm"
include "eqcomd.mm"
include "feq23d.mm"
include "mpbird.mm"
include "wb.mm"
include "fvexd.mm"
include "elmapg.mm"
include "coexg.mm"

theorem estrcco
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume estrcbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbas.u: |- ( ph -> U e. V )
  assume estrcco.o: |- .x. = ( comp ` C )
  assume estrcco.x: |- ( ph -> X e. U )
  assume estrcco.y: |- ( ph -> Y e. U )
  assume estrcco.z: |- ( ph -> Z e. U )
  assume estrcco.a: |- A = ( Base ` X )
  assume estrcco.b: |- B = ( Base ` Y )
  assume estrcco.d: |- D = ( Base ` Z )
  assume estrcco.f: |- ( ph -> F : A --> B )
  assume estrcco.g: |- ( ph -> G : B --> D )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) )

  proof
    wph
    vg
    vf
    cG
    cF
    cZ
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    cmap
    co
    #
    @1
    cX
    cbs
    cfv
    #
    cmap
    co
    #
    vg
    cv
    #
    vf
    cv
    #
    ccom
    #
    cG
    cF
    ccom
    #
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    cvv
    wph
    vv
    vz
    @9
    cZ
    cU
    cU
    cxp
    #
    cU
    vg
    vf
    vz
    cv
    #
    cbs
    cfv
    #
    vv
    cv
    #
    c2nd
    cfv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    @15
    @13
    c1st
    cfv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    @7
    cmpt2
    vg
    vf
    @2
    @4
    @7
    cmpt2
    #
    c.x
    cvv
    wph
    vz
    vv
    cC
    c.x
    cU
    vf
    vg
    cV
    estrcbas.c
    estrcbas.u
    estrcco.o
    estrccofval
    wph
    @13
    @9
    wceq
    #
    @11
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    vf
    @16
    @19
    @7
    @2
    @4
    @7
    @24
    @12
    @0
    @15
    @1
    cmap
    @23
    @12
    @0
    wceq
    #
    wph
    @22
    @25
    @21
    @11
    cZ
    cbs
    fveq2
    adantl
    adantl
    @24
    @14
    cY
    cbs
    @24
    @14
    @9
    c2nd
    cfv
    #
    cY
    @24
    @13
    @9
    c2nd
    wph
    @21
    @22
    simprl
    #
    fveq2d
    wph
    @26
    cY
    wceq
    #
    @23
    wph
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    @28
    estrcco.x
    estrcco.y
    cX
    cY
    cU
    cU
    op2ndg
    syl2anc
    adantr
    eqtrd
    fveq2d
    #
    oveq12d
    @24
    @15
    @1
    @18
    @3
    cmap
    @31
    @24
    @18
    @9
    c1st
    cfv
    #
    cbs
    cfv
    #
    @3
    @24
    @17
    @32
    cbs
    @24
    @13
    @9
    c1st
    @27
    fveq2d
    fveq2d
    wph
    @33
    @3
    wceq
    @23
    wph
    @32
    cX
    cbs
    wph
    @29
    @30
    @32
    cX
    wceq
    estrcco.x
    estrcco.y
    cX
    cY
    cU
    cU
    op1stg
    syl2anc
    fveq2d
    adantr
    eqtrd
    oveq12d
    @24
    @7
    eqidd
    mpt2eq123dv
    wph
    @29
    @30
    @9
    @10
    wcel
    estrcco.x
    estrcco.y
    cX
    cY
    cU
    cU
    opelxpi
    syl2anc
    estrcco.z
    @20
    cvv
    wcel
    wph
    vg
    vf
    @2
    @4
    @7
    @0
    @1
    cmap
    ovex
    @1
    @3
    cmap
    ovex
    mpt2ex
    a1i
    ovmpt2d
    @5
    cG
    wceq
    #
    @6
    cF
    wceq
    #
    wa
    #
    @7
    @8
    wceq
    wph
    @36
    @5
    cG
    @6
    cF
    @34
    @35
    simpl
    @34
    @35
    simpr
    coeq12d
    adantl
    wph
    cG
    @2
    wcel
    #
    @1
    @0
    cG
    wf
    #
    wph
    @38
    cB
    cD
    cG
    wf
    estrcco.g
    wph
    @1
    @0
    cB
    cD
    cG
    wph
    cB
    @1
    cB
    @1
    wceq
    wph
    estrcco.b
    a1i
    eqcomd
    #
    wph
    cD
    @0
    cD
    @0
    wceq
    wph
    estrcco.d
    a1i
    eqcomd
    feq23d
    mpbird
    wph
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    #
    @37
    @38
    wb
    wph
    cZ
    cbs
    fvexd
    wph
    cY
    cbs
    fvexd
    #
    @0
    @1
    cG
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    #
    wph
    cF
    @4
    wcel
    #
    @3
    @1
    cF
    wf
    #
    wph
    @44
    cA
    cB
    cF
    wf
    estrcco.f
    wph
    @3
    @1
    cA
    cB
    cF
    wph
    cA
    @3
    cA
    @3
    wceq
    wph
    estrcco.a
    a1i
    eqcomd
    @39
    feq23d
    mpbird
    wph
    @40
    @3
    cvv
    wcel
    @43
    @44
    wb
    @41
    wph
    cX
    cbs
    fvexd
    @1
    @3
    cF
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    #
    wph
    @37
    @43
    @8
    cvv
    wcel
    @42
    @45
    cG
    cF
    @2
    @4
    coexg
    syl2anc
    ovmpt2d
end
