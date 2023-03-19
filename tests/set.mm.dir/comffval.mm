include "cop.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "comfffval.mm"
include "a1i.mm"
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
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "opelxpi.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "ovmpt2d.mm"

theorem comffval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  assume comfffval.o: |- O = ( comf ` C )
  assume comfffval.b: |- B = ( Base ` C )
  assume comfffval.h: |- H = ( Hom ` C )
  assume comfffval.x: |- .x. = ( comp ` C )
  assume comffval.x: |- ( ph -> X e. B )
  assume comffval.y: |- ( ph -> Y e. B )
  assume comffval.z: |- ( ph -> Z e. B )

  disjoint f g
  disjoint C f
  disjoint C g
  disjoint f ph
  disjoint g ph
  disjoint .x. f
  disjoint .x. g
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint Z f
  disjoint Z g
  disjoint H f
  disjoint H g
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint c f
  disjoint c g
  disjoint C c
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph z
  disjoint .x. c
  disjoint .x. x
  disjoint .x. z
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  disjoint Z x
  disjoint Z z
  disjoint H c
  disjoint H x
  disjoint H z
  assert |- ( ph -> ( <. X , Y >. O Z ) = ( g e. ( Y H Z ) , f e. ( X H Y ) |-> ( g ( <. X , Y >. .x. Z ) f ) ) )

  proof
    wph
    vx
    vz
    cX
    cY
    cop
    #
    cZ
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vz
    cv
    #
    cH
    co
    #
    @2
    cH
    cfv
    #
    vg
    cv
    #
    vf
    cv
    #
    @2
    @4
    c.x
    co
    #
    co
    #
    cmpt2
    #
    vg
    vf
    cY
    cZ
    cH
    co
    #
    cX
    cY
    cH
    co
    #
    @7
    @8
    @0
    cZ
    c.x
    co
    #
    co
    #
    cmpt2
    #
    cO
    cvv
    cO
    vx
    vz
    @1
    cB
    @11
    cmpt2
    wceq
    wph
    vx
    vz
    cB
    cC
    c.x
    vf
    vg
    cH
    cO
    comfffval.o
    comfffval.b
    comfffval.h
    comfffval.x
    comfffval
    a1i
    wph
    @2
    @0
    wceq
    #
    @4
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    vf
    @5
    @6
    @10
    @12
    @13
    @15
    @20
    @3
    cY
    @4
    cZ
    cH
    @20
    @3
    @0
    c2nd
    cfv
    #
    cY
    @20
    @2
    @0
    c2nd
    wph
    @17
    @18
    simprl
    #
    fveq2d
    wph
    @21
    cY
    wceq
    #
    @19
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @23
    comffval.x
    comffval.y
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    wph
    @17
    @18
    simprr
    #
    oveq12d
    @20
    @6
    @0
    cH
    cfv
    @13
    @20
    @2
    @0
    cH
    @22
    fveq2d
    cX
    cY
    cH
    df-ov
    syl6eqr
    @20
    @9
    @14
    @7
    @8
    @20
    @2
    @0
    @4
    cZ
    c.x
    @22
    @26
    oveq12d
    oveqd
    mpt2eq123dv
    wph
    @24
    @25
    @0
    @1
    wcel
    comffval.x
    comffval.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    comffval.z
    @16
    cvv
    wcel
    wph
    vg
    vf
    @12
    @13
    @15
    cY
    cZ
    cH
    ovex
    cX
    cY
    cH
    ovex
    mpt2ex
    a1i
    ovmpt2d
end
