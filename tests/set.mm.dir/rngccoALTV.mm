include "crngh.mm"
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
include "rngccofvalALTV.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "wcel.mm"
include "op2ndg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simprr.mm"
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
include "coexg.mm"

theorem rngccoALTV
  let wph: wff ph
  let cB: class B
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
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume rngcbasALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcbasALTV.b: |- B = ( Base ` C )
  assume rngcbasALTV.u: |- ( ph -> U e. V )
  assume rngccofvalALTV.o: |- .x. = ( comp ` C )
  assume rngccoALTV.x: |- ( ph -> X e. B )
  assume rngccoALTV.y: |- ( ph -> Y e. B )
  assume rngccoALTV.z: |- ( ph -> Z e. B )
  assume rngccoALTV.f: |- ( ph -> F e. ( X RngHomo Y ) )
  assume rngccoALTV.g: |- ( ph -> G e. ( Y RngHomo Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) )

  proof
    wph
    vg
    vf
    cG
    cF
    cY
    cZ
    crngh
    co
    #
    cX
    cY
    crngh
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
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vv
    cv
    #
    c2nd
    cfv
    #
    vz
    cv
    #
    crngh
    co
    #
    @8
    c1st
    cfv
    #
    @9
    crngh
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
    cB
    cC
    c.x
    cU
    vf
    vg
    cV
    rngcbasALTV.c
    rngcbasALTV.b
    rngcbasALTV.u
    rngccofvalALTV.o
    rngccofvalALTV
    wph
    @8
    @6
    wceq
    #
    @10
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
    @9
    cY
    @10
    cZ
    crngh
    @18
    @9
    @6
    c2nd
    cfv
    #
    cY
    @18
    @8
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
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @21
    rngccoALTV.x
    rngccoALTV.y
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    #
    wph
    @15
    @16
    simprr
    oveq12d
    @18
    @12
    cX
    @9
    cY
    crngh
    @18
    @12
    @6
    c1st
    cfv
    #
    cX
    @18
    @8
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
    rngccoALTV.x
    rngccoALTV.y
    cX
    cY
    cB
    cB
    op1stg
    syl2anc
    adantr
    eqtrd
    @24
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
    rngccoALTV.x
    rngccoALTV.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    rngccoALTV.z
    @14
    cvv
    wcel
    wph
    vg
    vf
    @0
    @1
    @4
    cY
    cZ
    crngh
    ovex
    cX
    cY
    crngh
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
    rngccoALTV.g
    rngccoALTV.f
    wph
    cG
    @0
    wcel
    cF
    @1
    wcel
    @5
    cvv
    wcel
    rngccoALTV.g
    rngccoALTV.f
    cG
    cF
    @0
    @1
    coexg
    syl2anc
    ovmpt2d
end
