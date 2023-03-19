include "ccoa.mm"
include "cfv.mm"
include "cv.mm"
include "ccoda.mm"
include "cdoma.mm"
include "wceq.mm"
include "crab.mm"
include "c2nd.mm"
include "cop.mm"
include "co.mm"
include "cotp.mm"
include "cmpt2.mm"
include "ccat.mm"
include "wcel.mm"
include "carw.mm"
include "cco.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rabeqdv.mm"
include "oveqd.mm"
include "oteq3d.mm"
include "mpt2eq123dv.mm"
include "df-coa.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "dmmptss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "arwrcl.mm"
include "eq0rdv.mm"
include "eqidd.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem coafval
  let cA: class A
  let cC: class C
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vc: setvar c
  let cF: class F
  let cG: class G
  assume coafval.o: |- .x. = ( compA ` C )
  assume coafval.a: |- A = ( Arrow ` C )
  assume coafval.x: |- .xb = ( comp ` C )

  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint A c
  disjoint C c
  disjoint F g
  disjoint F h
  disjoint G g
  disjoint G h
  disjoint .xb c
  assert |- .x. = ( g e. A , f e. { h e. A | ( codA ` h ) = ( domA ` g ) } |-> <. ( domA ` f ) , ( codA ` g ) , ( ( 2nd ` g ) ( <. ( domA ` f ) , ( domA ` g ) >. .xb ( codA ` g ) ) ( 2nd ` f ) ) >. )

  proof
    c.x
    cC
    ccoa
    cfv
    #
    vg
    vf
    cA
    vh
    cv
    ccoda
    cfv
    vg
    cv
    #
    cdoma
    cfv
    #
    wceq
    #
    vh
    cA
    crab
    #
    vf
    cv
    #
    cdoma
    cfv
    #
    @1
    ccoda
    cfv
    #
    @1
    c2nd
    cfv
    #
    @5
    c2nd
    cfv
    #
    @6
    @2
    cop
    #
    @7
    c.xb
    co
    #
    co
    #
    cotp
    #
    cmpt2
    #
    coafval.o
    cC
    ccat
    wcel
    #
    @0
    @14
    wceq
    vc
    cC
    vg
    vf
    vc
    cv
    #
    carw
    cfv
    #
    @3
    vh
    @17
    crab
    #
    @6
    @7
    @8
    @9
    @10
    @7
    @16
    cco
    cfv
    #
    co
    #
    co
    #
    cotp
    #
    cmpt2
    #
    @14
    ccat
    ccoa
    @16
    cC
    wceq
    #
    vg
    vf
    @17
    @18
    @22
    cA
    @4
    @13
    @24
    @17
    cC
    carw
    cfv
    #
    cA
    @16
    cC
    carw
    fveq2
    coafval.a
    syl6eqr
    #
    @24
    @3
    vh
    @17
    cA
    @26
    rabeqdv
    @24
    @21
    @12
    @6
    @7
    @24
    @20
    @11
    @8
    @9
    @24
    @19
    c.xb
    @10
    @7
    @24
    @19
    cC
    cco
    cfv
    c.xb
    @16
    cC
    cco
    fveq2
    coafval.x
    syl6eqr
    oveqd
    oveqd
    oteq3d
    mpt2eq123dv
    vf
    vg
    vh
    vc
    df-coa
    #
    vg
    vf
    cA
    @4
    @13
    cA
    @25
    cvv
    coafval.a
    cC
    carw
    fvex
    eqeltri
    #
    @3
    vh
    cA
    @28
    rabex
    mpt2ex
    fvmpt
    @15
    wn
    #
    @0
    c0
    @14
    @29
    cC
    ccoa
    cdm
    #
    wcel
    #
    wn
    @0
    c0
    wceq
    @31
    @15
    @30
    ccat
    cC
    vc
    ccat
    @23
    ccoa
    @27
    dmmptss
    sseli
    con3i
    cC
    ccoa
    ndmfv
    syl
    @29
    @14
    vg
    vf
    c0
    @4
    @13
    cmpt2
    c0
    @29
    vg
    vf
    cA
    @4
    @13
    c0
    @4
    @13
    @29
    vf
    cA
    @5
    cA
    wcel
    @15
    cA
    cC
    @5
    coafval.a
    arwrcl
    con3i
    eq0rdv
    @29
    @4
    eqidd
    @29
    @13
    eqidd
    mpt2eq123dv
    vg
    vf
    @4
    @13
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
