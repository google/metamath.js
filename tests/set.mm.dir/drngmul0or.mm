include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cinvr.mm"
include "cfv.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "cur.mm"
include "cdr.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "crg.mm"
include "drngring.mm"
include "syl.mm"
include "drnginvrcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "adantlr.mm"
include "ringrz.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "ringlz.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "impbid.mm"

theorem drngmul0or
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume drngmuleq0.b: |- B = ( Base ` R )
  assume drngmuleq0.o: |- .0. = ( 0g ` R )
  assume drngmuleq0.t: |- .x. = ( .r ` R )
  assume drngmuleq0.r: |- ( ph -> R e. DivRing )
  assume drngmuleq0.x: |- ( ph -> X e. B )
  assume drngmuleq0.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( X .x. Y ) = .0. <-> ( X = .0. \/ Y = .0. ) ) )

  proof
    wph
    cX
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    cX
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
    wo
    #
    wph
    @1
    @4
    wph
    @1
    wa
    #
    @2
    @3
    @2
    wn
    cX
    c.0
    wne
    #
    @5
    @3
    cX
    c.0
    df-ne
    @5
    @6
    @3
    @5
    @6
    wa
    #
    cX
    cR
    cinvr
    cfv
    #
    cfv
    #
    @0
    c.x
    co
    #
    @9
    c.0
    c.x
    co
    #
    cY
    c.0
    @1
    @10
    @11
    wceq
    wph
    @6
    @0
    c.0
    @9
    c.x
    oveq2
    ad2antlr
    wph
    @6
    @10
    cY
    wceq
    @1
    wph
    @6
    wa
    #
    @9
    cX
    c.x
    co
    #
    cY
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cY
    c.x
    co
    #
    @10
    cY
    @12
    @13
    @15
    cY
    c.x
    @12
    cR
    cdr
    wcel
    #
    cX
    cB
    wcel
    #
    @6
    @13
    @15
    wceq
    wph
    @17
    @6
    drngmuleq0.r
    adantr
    #
    wph
    @18
    @6
    drngmuleq0.x
    adantr
    #
    wph
    @6
    simpr
    #
    cB
    cR
    c.x
    @15
    @8
    cX
    c.0
    drngmuleq0.b
    drngmuleq0.o
    drngmuleq0.t
    @15
    eqid
    #
    @8
    eqid
    #
    drnginvrl
    syl3anc
    oveq1d
    @12
    cR
    crg
    wcel
    #
    @9
    cB
    wcel
    #
    @18
    cY
    cB
    wcel
    #
    @14
    @10
    wceq
    wph
    @24
    @6
    wph
    @17
    @24
    drngmuleq0.r
    cR
    drngring
    syl
    #
    adantr
    @12
    @17
    @18
    @6
    @25
    @19
    @20
    @21
    cB
    cR
    @8
    cX
    c.0
    drngmuleq0.b
    drngmuleq0.o
    @23
    drnginvrcl
    syl3anc
    #
    @20
    wph
    @26
    @6
    drngmuleq0.y
    adantr
    cB
    cR
    c.x
    @9
    cX
    cY
    drngmuleq0.b
    drngmuleq0.t
    ringass
    syl13anc
    wph
    @16
    cY
    wceq
    #
    @6
    wph
    @24
    @26
    @29
    @27
    drngmuleq0.y
    cB
    cR
    c.x
    @15
    cY
    drngmuleq0.b
    drngmuleq0.t
    @22
    ringlidm
    syl2anc
    adantr
    3eqtr3d
    adantlr
    @7
    @24
    @25
    @11
    c.0
    wceq
    @5
    @24
    @6
    wph
    @24
    @1
    @27
    adantr
    adantr
    wph
    @6
    @25
    @1
    @28
    adantlr
    cB
    cR
    c.x
    @9
    c.0
    drngmuleq0.b
    drngmuleq0.t
    drngmuleq0.o
    ringrz
    syl2anc
    3eqtr3d
    ex
    syl5bir
    orrd
    ex
    wph
    @2
    @1
    @3
    wph
    @1
    @2
    c.0
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    wph
    @24
    @26
    @31
    @27
    drngmuleq0.y
    cB
    cR
    c.x
    cY
    c.0
    drngmuleq0.b
    drngmuleq0.t
    drngmuleq0.o
    ringlz
    syl2anc
    @2
    @0
    @30
    c.0
    cX
    c.0
    cY
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    wph
    @1
    @3
    cX
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    wph
    @24
    @18
    @33
    @27
    drngmuleq0.x
    cB
    cR
    c.x
    cX
    c.0
    drngmuleq0.b
    drngmuleq0.t
    drngmuleq0.o
    ringrz
    syl2anc
    @3
    @0
    @32
    c.0
    cY
    c.0
    cX
    c.x
    oveq2
    eqeq1d
    syl5ibrcom
    jaod
    impbid
end
