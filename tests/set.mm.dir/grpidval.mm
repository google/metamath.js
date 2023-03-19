include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "cvv.mm"
include "cbs.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "iotabidv.mm"
include "df-0g.mm"
include "iotaex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "weu.mm"
include "wex.mm"
include "euex.mm"
include "n0i.mm"
include "syl5eq.mm"
include "nsyl2.mm"
include "adantr.mm"
include "exlimiv.mm"
include "syl.mm"
include "con3i.mm"
include "iotanul.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem grpidval
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let ve: setvar e
  let cG: class G
  let c.0: class .0.
  let vg: setvar g
  assume grpidval.b: |- B = ( Base ` G )
  assume grpidval.p: |- .+ = ( +g ` G )
  assume grpidval.o: |- .0. = ( 0g ` G )

  disjoint e x
  disjoint B e
  disjoint B x
  disjoint G e
  disjoint G x
  disjoint e g
  disjoint g x
  disjoint B g
  disjoint G g
  disjoint .+ g
  assert |- .0. = ( iota e ( e e. B /\ A. x e. B ( ( e .+ x ) = x /\ ( x .+ e ) = x ) ) )

  proof
    c.0
    cG
    c0g
    cfv
    #
    ve
    cv
    #
    cB
    wcel
    #
    @1
    vx
    cv
    #
    c.pl
    co
    #
    @3
    wceq
    #
    @3
    @1
    c.pl
    co
    #
    @3
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    #
    ve
    cio
    #
    grpidval.o
    cG
    cvv
    wcel
    #
    @0
    @11
    wceq
    vg
    cG
    @1
    vg
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @1
    @3
    @13
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @1
    @16
    co
    #
    @3
    wceq
    #
    wa
    #
    vx
    @14
    wral
    #
    wa
    #
    ve
    cio
    @11
    cvv
    c0g
    @13
    cG
    wceq
    #
    @23
    @10
    ve
    @24
    @15
    @2
    @22
    @9
    @24
    @14
    cB
    @1
    @24
    @14
    cG
    cbs
    cfv
    #
    cB
    @13
    cG
    cbs
    fveq2
    grpidval.b
    syl6eqr
    #
    eleq2d
    @24
    @21
    @8
    vx
    @14
    cB
    @26
    @24
    @18
    @5
    @20
    @7
    @24
    @17
    @4
    @3
    @24
    @16
    c.pl
    @1
    @3
    @24
    @16
    cG
    cplusg
    cfv
    c.pl
    @13
    cG
    cplusg
    fveq2
    grpidval.p
    syl6eqr
    #
    oveqd
    eqeq1d
    @24
    @19
    @6
    @3
    @24
    @16
    c.pl
    @3
    @1
    @27
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    anbi12d
    iotabidv
    vx
    ve
    vg
    df-0g
    @10
    ve
    iotaex
    fvmpt
    @12
    wn
    #
    @0
    c0
    @11
    cG
    c0g
    fvprc
    @28
    @10
    ve
    weu
    #
    wn
    @11
    c0
    wceq
    @29
    @12
    @29
    @10
    ve
    wex
    @12
    @10
    ve
    euex
    @10
    @12
    ve
    @2
    @12
    @9
    @2
    cB
    c0
    wceq
    @12
    cB
    @1
    n0i
    @28
    cB
    @25
    c0
    grpidval.b
    cG
    cbs
    fvprc
    syl5eq
    nsyl2
    adantr
    exlimiv
    syl
    con3i
    @10
    ve
    iotanul
    syl
    eqtr4d
    pm2.61i
    eqtri
end
