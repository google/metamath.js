include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "cmpt2.mm"
include "setccofval.mm"
include "wceq.mm"
include "wa.mm"
include "simprr.mm"
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
include "coeq12d.mm"
include "wf.mm"
include "elmapd.mm"
include "mpbird.mm"
include "coexg.mm"

theorem setcco
  let wph: wff ph
  let cC: class C
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
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume setcbas.c: |- C = ( SetCat ` U )
  assume setcbas.u: |- ( ph -> U e. V )
  assume setcco.o: |- .x. = ( comp ` C )
  assume setcco.x: |- ( ph -> X e. U )
  assume setcco.y: |- ( ph -> Y e. U )
  assume setcco.z: |- ( ph -> Z e. U )
  assume setcco.f: |- ( ph -> F : X --> Y )
  assume setcco.g: |- ( ph -> G : Y --> Z )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) )

  proof
    wph
    vg
    vf
    cG
    cF
    cZ
    cY
    cmap
    co
    #
    cY
    cX
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
    @6
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
    vv
    cv
    #
    c2nd
    cfv
    #
    cmap
    co
    #
    @10
    @9
    c1st
    cfv
    #
    cmap
    co
    #
    @4
    cmpt2
    vg
    vf
    @0
    @1
    @4
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
    setcbas.c
    setcbas.u
    setcco.o
    setccofval
    wph
    @9
    @6
    wceq
    #
    @8
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    vf
    @11
    @13
    @4
    @0
    @1
    @4
    @18
    @8
    cZ
    @10
    cY
    cmap
    wph
    @15
    @16
    simprr
    @18
    @10
    @6
    c2nd
    cfv
    #
    cY
    @18
    @9
    @6
    c2nd
    wph
    @15
    @16
    simprl
    #
    fveq2d
    wph
    @19
    cY
    wceq
    #
    @17
    wph
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    @21
    setcco.x
    setcco.y
    cX
    cY
    cU
    cU
    op2ndg
    syl2anc
    adantr
    eqtrd
    #
    oveq12d
    @18
    @10
    cY
    @12
    cX
    cmap
    @24
    @18
    @12
    @6
    c1st
    cfv
    #
    cX
    @18
    @9
    @6
    c1st
    @20
    fveq2d
    wph
    @25
    cX
    wceq
    #
    @17
    wph
    @22
    @23
    @26
    setcco.x
    setcco.y
    cX
    cY
    cU
    cU
    op1stg
    syl2anc
    adantr
    eqtrd
    oveq12d
    @18
    @4
    eqidd
    mpt2eq123dv
    wph
    @22
    @23
    @6
    @7
    wcel
    setcco.x
    setcco.y
    cX
    cY
    cU
    cU
    opelxpi
    syl2anc
    setcco.z
    @14
    cvv
    wcel
    wph
    vg
    vf
    @0
    @1
    @4
    cZ
    cY
    cmap
    ovex
    cY
    cX
    cmap
    ovex
    mpt2ex
    a1i
    ovmpt2d
    wph
    @2
    cG
    wceq
    #
    @3
    cF
    wceq
    #
    wa
    wa
    @2
    cG
    @3
    cF
    wph
    @27
    @28
    simprl
    wph
    @27
    @28
    simprr
    coeq12d
    wph
    cG
    @0
    wcel
    #
    cY
    cZ
    cG
    wf
    setcco.g
    wph
    cZ
    cY
    cG
    cU
    cU
    setcco.z
    setcco.y
    elmapd
    mpbird
    #
    wph
    cF
    @1
    wcel
    #
    cX
    cY
    cF
    wf
    setcco.f
    wph
    cY
    cX
    cF
    cU
    cU
    setcco.y
    setcco.x
    elmapd
    mpbird
    #
    wph
    @29
    @31
    @5
    cvv
    wcel
    @30
    @32
    cG
    cF
    @0
    @1
    coexg
    syl2anc
    ovmpt2d
end
