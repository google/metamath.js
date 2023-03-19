include "cvv.mm"
include "wcel.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmps.mm"
include "crab.mm"
include "eqtr3d.mm"
include "psrbaspropd.mm"
include "adantr.mm"
include "wb.mm"
include "grpidpropd.mm"
include "breq2d.mm"
include "rabeqbidv.mm"
include "eqid.mm"
include "mplbas.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "reldmmpl.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem mplbaspropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vc: setvar c
  assume psrplusgpropd.b1: |- ( ph -> B = ( Base ` R ) )
  assume psrplusgpropd.b2: |- ( ph -> B = ( Base ` S ) )
  assume psrplusgpropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` R ) y ) = ( x ( +g ` S ) y ) )

  disjoint ph y
  disjoint ph x
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R y
  disjoint R x
  disjoint S y
  disjoint S x
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint a b
  disjoint a d
  disjoint a y
  disjoint b d
  disjoint b y
  disjoint d y
  disjoint I a
  disjoint I b
  disjoint I d
  disjoint I c
  disjoint R a
  disjoint R b
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S d
  disjoint a x
  disjoint c d
  disjoint d x
  assert |- ( ph -> ( Base ` ( I mPoly R ) ) = ( Base ` ( I mPoly S ) ) )

  proof
    wph
    cI
    cvv
    wcel
    #
    cI
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    cI
    cS
    cmpl
    co
    #
    cbs
    cfv
    #
    wceq
    #
    wph
    @0
    wa
    #
    va
    cv
    #
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    va
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    crab
    @7
    cS
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    va
    cI
    cS
    cmps
    co
    #
    cbs
    cfv
    #
    crab
    @2
    @4
    @6
    @9
    @13
    va
    @11
    @15
    wph
    @11
    @15
    wceq
    @0
    wph
    cR
    cS
    cI
    wph
    cB
    cR
    cbs
    cfv
    cS
    cbs
    cfv
    psrplusgpropd.b1
    psrplusgpropd.b2
    eqtr3d
    psrbaspropd
    adantr
    wph
    @9
    @13
    wb
    @0
    wph
    @8
    @12
    @7
    cfsupp
    wph
    vx
    vy
    cB
    cR
    cS
    psrplusgpropd.b1
    psrplusgpropd.b2
    psrplusgpropd.p
    grpidpropd
    breq2d
    adantr
    rabeqbidv
    @11
    @1
    cR
    @10
    @2
    va
    cI
    @8
    @1
    eqid
    @10
    eqid
    @11
    eqid
    @8
    eqid
    @2
    eqid
    mplbas
    @15
    @3
    cS
    @14
    @4
    va
    cI
    @12
    @3
    eqid
    @14
    eqid
    @15
    eqid
    @12
    eqid
    @4
    eqid
    mplbas
    3eqtr4g
    @0
    wn
    #
    @5
    wph
    @16
    @1
    @3
    cbs
    @16
    @1
    c0
    @3
    cI
    cR
    cmpl
    reldmmpl
    ovprc1
    cI
    cS
    cmpl
    reldmmpl
    ovprc1
    eqtr4d
    fveq2d
    adantl
    pm2.61dan
end
