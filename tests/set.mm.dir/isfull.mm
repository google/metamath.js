include "cful.mm"
include "co.mm"
include "wbr.mm"
include "cfunc.mm"
include "cv.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "fullfunc.mm"
include "ssbri.mm"
include "wa.mm"
include "copab.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "df-br.mm"
include "funcrcl.mm"
include "sylbi.mm"
include "chom.mm"
include "cbs.mm"
include "oveq12.mm"
include "breqd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "df-full.mm"
include "ovex.mm"
include "ssopab2i.mm"
include "opabss.mm"
include "sstri.mm"
include "ssexi.mm"
include "ovmpt2a.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "wrel.mm"
include "relfunc.mm"
include "brrelex12.mm"
include "mpan.mm"
include "breq12.mm"
include "rneqd.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "eqid.mm"
include "brabga.mm"
include "bitrd.mm"
include "bianabs.mm"
include "biadan2.mm"

theorem isfull
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let wph: wff ph
  let cH: class H
  let cR: class R
  let cX: class X
  let cY: class Y
  assume isfull.b: |- B = ( Base ` C )
  assume isfull.j: |- J = ( Hom ` D )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint J x
  disjoint J y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint d y
  disjoint B d
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C g
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D g
  disjoint ph x
  disjoint ph y
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint J c
  disjoint J d
  disjoint J f
  disjoint J g
  disjoint R f
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  assert |- ( F ( C Full D ) G <-> ( F ( C Func D ) G /\ A. x e. B A. y e. B ran ( x G y ) = ( ( F ` x ) J ( F ` y ) ) ) )

  proof
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    crn
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cJ
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @0
    @2
    cF
    cG
    cC
    cD
    fullfunc
    ssbri
    @3
    @1
    @12
    @3
    @1
    cF
    cG
    vf
    cv
    #
    vg
    cv
    #
    @2
    wbr
    #
    @4
    @5
    @14
    co
    #
    crn
    #
    @4
    @13
    cfv
    #
    @5
    @13
    cfv
    #
    cJ
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    wbr
    #
    @3
    @12
    wa
    #
    @3
    @0
    @25
    cF
    cG
    @3
    cC
    ccat
    wcel
    cD
    ccat
    wcel
    wa
    #
    @0
    @25
    wceq
    @3
    cF
    cG
    cop
    #
    @2
    wcel
    @28
    cF
    cG
    @2
    df-br
    cC
    cD
    @29
    funcrcl
    sylbi
    vc
    vd
    cC
    cD
    ccat
    ccat
    @13
    @14
    vc
    cv
    #
    vd
    cv
    #
    cfunc
    co
    #
    wbr
    #
    @17
    @18
    @19
    @31
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    @30
    cbs
    cfv
    #
    wral
    #
    vx
    @37
    wral
    #
    wa
    #
    vf
    vg
    copab
    @25
    cful
    @30
    cC
    wceq
    #
    @31
    cD
    wceq
    #
    wa
    #
    @40
    @24
    vf
    vg
    @43
    @33
    @15
    @39
    @23
    @43
    @32
    @2
    @13
    @14
    @30
    cC
    @31
    cD
    cfunc
    oveq12
    breqd
    @43
    @38
    @22
    vx
    @37
    cB
    @43
    @37
    cC
    cbs
    cfv
    cB
    @43
    @30
    cC
    cbs
    @41
    @42
    simpl
    fveq2d
    isfull.b
    syl6eqr
    #
    @43
    @36
    @21
    vy
    @37
    cB
    @44
    @43
    @35
    @20
    @17
    @43
    @34
    cJ
    @18
    @19
    @43
    @34
    cD
    chom
    cfv
    cJ
    @43
    @31
    cD
    chom
    @41
    @42
    simpr
    fveq2d
    isfull.j
    syl6eqr
    oveqd
    eqeq2d
    raleqbidv
    raleqbidv
    anbi12d
    opabbidv
    vx
    vy
    vf
    vg
    vc
    vd
    df-full
    @25
    @2
    cC
    cD
    cfunc
    ovex
    @25
    @15
    vf
    vg
    copab
    @2
    @24
    @15
    vf
    vg
    @15
    @23
    simpl
    ssopab2i
    vf
    vg
    @2
    opabss
    sstri
    ssexi
    ovmpt2a
    syl
    breqd
    @3
    cF
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    @26
    @27
    wb
    @2
    wrel
    @3
    @45
    cC
    cD
    relfunc
    cF
    cG
    @2
    brrelex12
    mpan
    @24
    @27
    vf
    vg
    cF
    cG
    @25
    cvv
    cvv
    @13
    cF
    wceq
    #
    @14
    cG
    wceq
    #
    wa
    #
    @15
    @3
    @23
    @12
    @13
    cF
    @14
    cG
    @2
    breq12
    @48
    @21
    @11
    vx
    vy
    cB
    cB
    @48
    @17
    @7
    @20
    @10
    @48
    @16
    @6
    @48
    @14
    cG
    @4
    @5
    @46
    @47
    simpr
    oveqd
    rneqd
    @48
    @18
    @8
    @19
    @9
    cJ
    @48
    @4
    @13
    cF
    @46
    @47
    simpl
    #
    fveq1d
    @48
    @5
    @13
    cF
    @49
    fveq1d
    oveq12d
    eqeq12d
    2ralbidv
    anbi12d
    @25
    eqid
    brabga
    syl
    bitrd
    bianabs
    biadan2
end
