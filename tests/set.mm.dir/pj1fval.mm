include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cpw.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cvv.mm"
include "cpj1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "cbs.mm"
include "clsm.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "df-pj1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "rexeqdv.mm"
include "riotaeqbidv.mm"
include "simp2.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simp3.mm"
include "ovex.mm"
include "mptex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem pj1fval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let cX: class X
  assume pj1fval.v: |- B = ( Base ` G )
  assume pj1fval.a: |- .+ = ( +g ` G )
  assume pj1fval.s: |- .(+) = ( LSSum ` G )
  assume pj1fval.p: |- P = ( proj1 ` G )

  disjoint .+ z
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint g t
  disjoint g u
  disjoint g z
  disjoint .+ g
  disjoint t u
  disjoint t z
  disjoint .+ t
  disjoint u z
  disjoint .+ u
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint t x
  disjoint t y
  disjoint B t
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint T t
  disjoint T u
  disjoint U t
  disjoint U u
  disjoint .(+) g
  disjoint .(+) t
  disjoint .(+) u
  disjoint G g
  disjoint G t
  disjoint G u
  disjoint V t
  disjoint V u
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( G e. V /\ T C_ B /\ U C_ B ) -> ( T P U ) = ( z e. ( T .(+) U ) |-> ( iota_ x e. T E. y e. U z = ( x .+ y ) ) ) )

  proof
    cG
    cV
    wcel
    #
    cT
    cB
    wss
    #
    cU
    cB
    wss
    #
    w3a
    #
    vt
    vu
    cT
    cU
    cB
    cpw
    #
    @4
    vz
    vt
    cv
    #
    vu
    cv
    #
    c.po
    co
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vy
    @6
    wrex
    #
    vx
    @5
    crio
    #
    cmpt
    #
    vz
    cT
    cU
    c.po
    co
    #
    @12
    vy
    cU
    wrex
    #
    vx
    cT
    crio
    #
    cmpt
    #
    cP
    cvv
    @3
    cP
    cG
    cpj1
    cfv
    #
    vt
    vu
    @4
    @4
    @15
    cmpt2
    #
    pj1fval.p
    @3
    cG
    cvv
    wcel
    #
    @20
    @21
    wceq
    @0
    @1
    @22
    @2
    cG
    cV
    elex
    3ad2ant1
    vg
    cG
    vt
    vu
    vg
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @25
    vz
    @5
    @6
    @23
    clsm
    cfv
    #
    co
    #
    @8
    @9
    @10
    @23
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @6
    wrex
    #
    vx
    @5
    crio
    #
    cmpt
    #
    cmpt2
    @21
    cvv
    cpj1
    @23
    cG
    wceq
    #
    vt
    vu
    @25
    @25
    @33
    @4
    @4
    @15
    @34
    @24
    cB
    @34
    @24
    cG
    cbs
    cfv
    #
    cB
    @23
    cG
    cbs
    fveq2
    pj1fval.v
    syl6eqr
    pweqd
    #
    @36
    @34
    vz
    @27
    @32
    @7
    @14
    @34
    @26
    c.po
    @5
    @6
    @34
    @26
    cG
    clsm
    cfv
    c.po
    @23
    cG
    clsm
    fveq2
    pj1fval.s
    syl6eqr
    oveqd
    @34
    @31
    @13
    vx
    @5
    @34
    @30
    @12
    vy
    @6
    @34
    @29
    @11
    @8
    @34
    @28
    c.pl
    @9
    @10
    @34
    @28
    cG
    cplusg
    cfv
    c.pl
    @23
    cG
    cplusg
    fveq2
    pj1fval.a
    syl6eqr
    oveqd
    eqeq2d
    rexbidv
    riotabidv
    mpteq12dv
    mpt2eq123dv
    vx
    vy
    vz
    vg
    vu
    vt
    df-pj1
    vt
    vu
    @4
    @4
    @15
    cB
    cB
    @35
    cvv
    pj1fval.v
    cG
    cbs
    fvex
    eqeltri
    #
    pwex
    #
    @38
    mpt2ex
    fvmpt
    syl
    syl5eq
    @3
    @5
    cT
    wceq
    #
    @6
    cU
    wceq
    #
    wa
    #
    wa
    #
    vz
    @7
    @14
    @16
    @18
    @41
    @7
    @16
    wceq
    @3
    @5
    cT
    @6
    cU
    c.po
    oveq12
    adantl
    @42
    @13
    @17
    vx
    @5
    cT
    @3
    @39
    @40
    simprl
    @42
    @12
    vy
    @6
    cU
    @3
    @39
    @40
    simprr
    rexeqdv
    riotaeqbidv
    mpteq12dv
    @3
    @1
    cT
    @4
    wcel
    @0
    @1
    @2
    simp2
    cT
    cB
    @37
    elpw2
    sylibr
    @3
    @2
    cU
    @4
    wcel
    @0
    @1
    @2
    simp3
    cU
    cB
    @37
    elpw2
    sylibr
    @19
    cvv
    wcel
    @3
    vz
    @16
    @18
    cT
    cU
    c.po
    ovex
    mptex
    a1i
    ovmpt2d
end
