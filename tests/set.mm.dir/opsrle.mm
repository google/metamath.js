include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wo.mm"
include "copab.mm"
include "cple.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "cxp.mm"
include "adantr.mm"
include "opsrval.mm"
include "fveq2d.mm"
include "cmps.mm"
include "ovex.mm"
include "eqeltri.mm"
include "cbs.mm"
include "fvex.mm"
include "xpex.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstr3i.mm"
include "ssexi.mm"
include "pleid.mm"
include "setsid.mm"
include "mp2an.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "copws.mm"
include "reldmopsr.mm"
include "ovprc.mm"
include "adantl.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "0fv.mm"
include "syl6eq.mm"
include "str0.mm"
include "reldmpsr.mm"
include "base0.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "sseq0.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem opsrle
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cT: class T
  let vh: setvar h
  let cI: class I
  let c.le: class .<_
  let cO: class O
  assume opsrle.s: |- S = ( I mPwSer R )
  assume opsrle.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrle.b: |- B = ( Base ` S )
  assume opsrle.q: |- .< = ( lt ` R )
  assume opsrle.c: |- C = ( T <bag I )
  assume opsrle.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume opsrle.l: |- .<_ = ( le ` O )
  assume opsrle.t: |- ( ph -> T C_ ( I X. I ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint D w
  disjoint D z
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint w x
  disjoint w y
  disjoint I w
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> .<_ = { <. x , y >. | ( { x , y } C_ B /\ ( E. z e. D ( ( x ` z ) .< ( y ` z ) /\ A. w e. D ( w C z -> ( x ` w ) = ( y ` w ) ) ) \/ x = y ) ) } )

  proof
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    c.le
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cB
    wss
    #
    vz
    cv
    #
    @3
    cfv
    @6
    @4
    cfv
    c.lt
    wbr
    vw
    cv
    #
    @6
    cC
    wbr
    @7
    @3
    cfv
    @7
    @4
    cfv
    wceq
    wi
    vw
    cD
    wral
    wa
    vz
    cD
    wrex
    @3
    @4
    wceq
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    wceq
    wph
    @2
    wa
    #
    cO
    cple
    cfv
    #
    cS
    cnx
    cple
    cfv
    #
    @10
    cop
    csts
    co
    #
    cple
    cfv
    #
    c.le
    @10
    @11
    cO
    @14
    cple
    @11
    vx
    vy
    vz
    vw
    cB
    cC
    cD
    cR
    cS
    c.lt
    cT
    vh
    cI
    @10
    cO
    cvv
    cvv
    opsrle.s
    opsrle.o
    opsrle.b
    opsrle.q
    opsrle.c
    opsrle.d
    @10
    eqid
    wph
    @0
    @1
    simprl
    wph
    @0
    @1
    simprr
    wph
    cT
    cI
    cI
    cxp
    wss
    @2
    opsrle.t
    adantr
    opsrval
    fveq2d
    opsrle.l
    cS
    cvv
    wcel
    @10
    cvv
    wcel
    @10
    @15
    wceq
    cS
    cI
    cR
    cmps
    co
    #
    cvv
    opsrle.s
    cI
    cR
    cmps
    ovex
    eqeltri
    @10
    cB
    cB
    cxp
    #
    cB
    cB
    cB
    cS
    cbs
    cfv
    #
    cvv
    opsrle.b
    cS
    cbs
    fvex
    eqeltri
    #
    @19
    xpex
    @10
    @3
    cB
    wcel
    @4
    cB
    wcel
    wa
    #
    @8
    wa
    #
    vx
    vy
    copab
    @17
    @21
    @9
    vx
    vy
    @20
    @5
    @8
    @3
    @4
    cB
    vx
    vex
    vy
    vex
    prss
    anbi1i
    opabbii
    @8
    vx
    vy
    cB
    cB
    opabssxp
    eqsstr3i
    #
    ssexi
    cvv
    @10
    cple
    cvv
    cS
    pleid
    setsid
    mp2an
    3eqtr4g
    wph
    @2
    wn
    #
    wa
    #
    c.le
    c0
    @10
    @24
    @12
    c0
    cple
    cfv
    c.le
    c0
    @24
    cO
    c0
    cple
    @24
    cO
    cT
    c0
    cfv
    #
    c0
    @24
    cO
    cT
    cI
    cR
    copws
    co
    #
    cfv
    @25
    opsrle.o
    @24
    cT
    @26
    c0
    @23
    @26
    c0
    wceq
    wph
    cI
    cR
    copws
    reldmopsr
    ovprc
    adantl
    fveq1d
    syl5eq
    cT
    0fv
    syl6eq
    fveq2d
    opsrle.l
    cple
    @13
    pleid
    str0
    3eqtr4g
    @24
    @10
    @17
    wss
    @17
    c0
    wceq
    @10
    c0
    wceq
    @22
    @24
    @17
    cB
    c0
    cxp
    c0
    @24
    cB
    c0
    cB
    @24
    @18
    c0
    cbs
    cfv
    cB
    c0
    @24
    cS
    c0
    cbs
    @24
    cS
    @16
    c0
    opsrle.s
    @23
    @16
    c0
    wceq
    wph
    cI
    cR
    cmps
    reldmpsr
    ovprc
    adantl
    syl5eq
    fveq2d
    opsrle.b
    base0
    3eqtr4g
    xpeq2d
    cB
    xp0
    syl6eq
    @10
    @17
    sseq0
    sylancr
    eqtr4d
    pm2.61dan
end
