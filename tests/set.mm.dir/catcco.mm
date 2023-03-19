include "cfunc.mm"
include "co.mm"
include "cv.mm"
include "ccofu.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cfv.mm"
include "cmpt2.mm"
include "catccofval.mm"
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
include "df-ov.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "opelxpi.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"

theorem catcco
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
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  assume catcbas.c: |- C = ( CatCat ` U )
  assume catcbas.b: |- B = ( Base ` C )
  assume catcbas.u: |- ( ph -> U e. V )
  assume catcco.o: |- .x. = ( comp ` C )
  assume catcco.x: |- ( ph -> X e. B )
  assume catcco.y: |- ( ph -> Y e. B )
  assume catcco.z: |- ( ph -> Z e. B )
  assume catcco.f: |- ( ph -> F e. ( X Func Y ) )
  assume catcco.g: |- ( ph -> G e. ( Y Func Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o.func F ) )

  proof
    wph
    vg
    vf
    cG
    cF
    cY
    cZ
    cfunc
    co
    #
    cX
    cY
    cfunc
    co
    #
    vg
    cv
    #
    vf
    cv
    #
    ccofu
    co
    #
    cG
    cF
    ccofu
    co
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
    cfunc
    co
    #
    @8
    cfunc
    cfv
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
    catcbas.c
    catcbas.b
    catcbas.u
    catcco.o
    catccofval
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
    @12
    @4
    @0
    @1
    @4
    @17
    @9
    cY
    @10
    cZ
    cfunc
    @17
    @9
    @6
    c2nd
    cfv
    #
    cY
    @17
    @8
    @6
    c2nd
    wph
    @14
    @15
    simprl
    #
    fveq2d
    wph
    @18
    cY
    wceq
    #
    @16
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @20
    catcco.x
    catcco.y
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    wph
    @14
    @15
    simprr
    oveq12d
    @17
    @12
    @6
    cfunc
    cfv
    @1
    @17
    @8
    @6
    cfunc
    @19
    fveq2d
    cX
    cY
    cfunc
    df-ov
    syl6eqr
    @17
    @4
    eqidd
    mpt2eq123dv
    wph
    @21
    @22
    @6
    @7
    wcel
    catcco.x
    catcco.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    catcco.z
    @13
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
    cfunc
    ovex
    cX
    cY
    cfunc
    ovex
    mpt2ex
    a1i
    ovmpt2d
    @2
    cG
    wceq
    @3
    cF
    wceq
    wa
    @4
    @5
    wceq
    wph
    @2
    cG
    @3
    cF
    ccofu
    oveq12
    adantl
    catcco.g
    catcco.f
    wph
    cG
    cF
    ccofu
    ovexd
    ovmpt2d
end
