include "wcel.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cmpt.mm"
include "csb.mm"
include "cvv.mm"
include "cvtxdg.mm"
include "df-vtxdg.mm"
include "a1i.mm"
include "wa.mm"
include "fvex.mm"
include "simpl.mm"
include "dmeq.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "mpteq12dv.mm"
include "csbie2.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "elex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "fvmptd.mm"

theorem vtxdgfval
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vg: setvar g
  let vv: setvar v
  assume vtxdgfval.v: |- V = ( Vtx ` G )
  assume vtxdgfval.i: |- I = ( iEdg ` G )
  assume vtxdgfval.a: |- A = dom I

  disjoint u x
  disjoint A x
  disjoint G u
  disjoint G x
  disjoint V u
  disjoint e g
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint u v
  disjoint v x
  disjoint A g
  disjoint G g
  disjoint I g
  disjoint V g
  disjoint W g
  assert |- ( G e. W -> ( VtxDeg ` G ) = ( u e. V |-> ( ( # ` { x e. A | u e. ( I ` x ) } ) +e ( # ` { x e. A | ( I ` x ) = { u } } ) ) ) )

  proof
    cG
    cW
    wcel
    #
    vg
    cG
    vv
    vg
    cv
    #
    cvtx
    cfv
    #
    ve
    @1
    ciedg
    cfv
    #
    vu
    vv
    cv
    #
    vu
    cv
    #
    vx
    cv
    #
    ve
    cv
    #
    cfv
    #
    wcel
    #
    vx
    @7
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @8
    @5
    csn
    #
    wceq
    #
    vx
    @10
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    csb
    csb
    #
    vu
    cV
    @5
    @6
    cI
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    @20
    @13
    wceq
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    cvv
    cvtxdg
    cvv
    cvtxdg
    vg
    cvv
    @19
    cmpt
    wceq
    @0
    vx
    vv
    vu
    ve
    vg
    df-vtxdg
    a1i
    @0
    @1
    cG
    wceq
    #
    wa
    @19
    vu
    @2
    @5
    @6
    @3
    cfv
    #
    wcel
    #
    vx
    @3
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @30
    @13
    wceq
    #
    vx
    @32
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    @28
    vv
    ve
    @2
    @3
    @18
    @39
    @1
    cvtx
    fvex
    @1
    ciedg
    fvex
    @4
    @2
    wceq
    #
    @7
    @3
    wceq
    #
    wa
    vu
    @4
    @17
    @2
    @38
    @40
    @41
    simpl
    @41
    @17
    @38
    wceq
    @40
    @41
    @12
    @34
    @16
    @37
    cxad
    @41
    @11
    @33
    chash
    @41
    @9
    @31
    vx
    @10
    @32
    @7
    @3
    dmeq
    #
    @41
    @8
    @30
    @5
    @6
    @7
    @3
    fveq1
    #
    eleq2d
    rabeqbidv
    fveq2d
    @41
    @15
    @36
    chash
    @41
    @14
    @35
    vx
    @10
    @32
    @42
    @41
    @8
    @30
    @13
    @43
    eqeq1d
    rabeqbidv
    fveq2d
    oveq12d
    adantl
    mpteq12dv
    csbie2
    @29
    @39
    @28
    wceq
    @0
    @29
    vu
    @2
    @38
    cV
    @27
    @29
    @2
    cG
    cvtx
    cfv
    #
    cV
    @1
    cG
    cvtx
    fveq2
    vtxdgfval.v
    syl6eqr
    @29
    @34
    @23
    @37
    @26
    cxad
    @29
    @33
    @22
    chash
    @29
    @31
    @21
    vx
    @32
    cA
    @29
    @32
    cG
    ciedg
    cfv
    #
    cdm
    #
    cA
    @29
    @3
    @45
    @1
    cG
    ciedg
    fveq2
    #
    dmeqd
    cA
    cI
    cdm
    @46
    vtxdgfval.a
    cI
    @45
    vtxdgfval.i
    dmeqi
    eqtri
    syl6eqr
    #
    @29
    @30
    @20
    @5
    @29
    @6
    @3
    cI
    @29
    @3
    @45
    cI
    @47
    vtxdgfval.i
    syl6eqr
    fveq1d
    #
    eleq2d
    rabeqbidv
    fveq2d
    @29
    @36
    @25
    chash
    @29
    @35
    @24
    vx
    @32
    cA
    @48
    @29
    @30
    @20
    @13
    @49
    eqeq1d
    rabeqbidv
    fveq2d
    oveq12d
    mpteq12dv
    adantl
    syl5eq
    cG
    cW
    elex
    cV
    cvv
    wcel
    @28
    cvv
    wcel
    @0
    cV
    @44
    cvv
    vtxdgfval.v
    cG
    cvtx
    fvex
    eqeltri
    vu
    cV
    @27
    cvv
    mptexg
    mp1i
    fvmptd
end
