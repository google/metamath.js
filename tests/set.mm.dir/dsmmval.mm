include "wcel.mm"
include "cvv.mm"
include "cdsmm.mm"
include "co.mm"
include "cprds.mm"
include "cress.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "cbs.mm"
include "cixp.mm"
include "wa.mm"
include "oveq12.mm"
include "eqid.mm"
include "vex.mm"
include "a1i.mm"
include "eqidd.mm"
include "prdsbas.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "dmeqd.mm"
include "fveq1d.mm"
include "neeq2d.mm"
include "rabeqbidv.mm"
include "eleq1d.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "df-dsmm.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "reldmdsmm.mm"
include "ovprc1.mm"
include "ress0.mm"
include "reldmprds.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "pm2.61ian.mm"
include "syl.mm"

theorem dsmmval
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  assume dsmmval.b: |- B = { f e. ( Base ` ( S Xs_ R ) ) | { x e. dom R | ( f ` x ) =/= ( 0g ` ( R ` x ) ) } e. Fin }

  disjoint S f
  disjoint S x
  disjoint f x
  disjoint R f
  disjoint R x
  disjoint S s
  disjoint S r
  disjoint r s
  disjoint f s
  disjoint s x
  disjoint f r
  disjoint r x
  disjoint R s
  disjoint R r
  disjoint B s
  disjoint B r
  assert |- ( R e. V -> ( S (+)m R ) = ( ( S Xs_ R ) |`s B ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    #
    cS
    cR
    cdsmm
    co
    #
    cS
    cR
    cprds
    co
    #
    cB
    cress
    co
    #
    wceq
    #
    cR
    cV
    elex
    cS
    cvv
    wcel
    #
    @0
    @4
    vs
    vr
    cS
    cR
    cvv
    cvv
    vs
    cv
    #
    vr
    cv
    #
    cprds
    co
    #
    vx
    cv
    #
    vf
    cv
    cfv
    #
    @9
    @7
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    vx
    @7
    cdm
    #
    crab
    #
    cfn
    wcel
    #
    vf
    vx
    @14
    @11
    cbs
    cfv
    cixp
    #
    crab
    #
    cress
    co
    @3
    cdsmm
    @6
    cS
    wceq
    #
    @7
    cR
    wceq
    #
    wa
    #
    @8
    @2
    @18
    cB
    cress
    @6
    cS
    @7
    cR
    cprds
    oveq12
    #
    @21
    @18
    @10
    @9
    cR
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    vx
    cR
    cdm
    #
    crab
    #
    cfn
    wcel
    #
    vf
    @2
    cbs
    cfv
    #
    crab
    cB
    @21
    @16
    @28
    vf
    @17
    @29
    @21
    @8
    cbs
    cfv
    #
    @17
    @29
    @21
    vx
    @30
    @8
    @7
    @6
    @14
    cvv
    cvv
    @8
    eqid
    @6
    cvv
    wcel
    @21
    vs
    vex
    a1i
    @7
    cvv
    wcel
    @21
    vr
    vex
    a1i
    @30
    eqid
    @21
    @14
    eqidd
    prdsbas
    @21
    @8
    @2
    cbs
    @22
    fveq2d
    eqtr3d
    @21
    @15
    @27
    cfn
    @21
    @13
    @25
    vx
    @14
    @26
    @21
    @7
    cR
    @19
    @20
    simpr
    #
    dmeqd
    @21
    @12
    @24
    @10
    @21
    @11
    @23
    c0g
    @21
    @9
    @7
    cR
    @31
    fveq1d
    fveq2d
    neeq2d
    rabeqbidv
    eleq1d
    rabeqbidv
    dsmmval.b
    syl6eqr
    oveq12d
    vx
    vf
    vs
    vr
    df-dsmm
    @2
    cB
    cress
    ovex
    ovmpt2a
    @5
    wn
    #
    @4
    @0
    @32
    @1
    c0
    cB
    cress
    co
    #
    @3
    @32
    @1
    c0
    @33
    cS
    cR
    cdsmm
    reldmdsmm
    ovprc1
    cB
    ress0
    syl6eqr
    @32
    @2
    c0
    cB
    cress
    cS
    cR
    cprds
    reldmprds
    ovprc1
    oveq1d
    eqtr4d
    adantr
    pm2.61ian
    syl
end
