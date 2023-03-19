include "cidom.mm"
include "wcel.mm"
include "ccrg.mm"
include "cnzr.mm"
include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cdif.mm"
include "wral.mm"
include "w3a.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "simprbi.mm"
include "domnnzr.mm"
include "syl.mm"
include "wa.mm"
include "simpl.mm"
include "wne.mm"
include "eldifsn.mm"
include "adantl.mm"
include "fta1g.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "simp1.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cbs.mm"
include "simp2.mm"
include "wn.mm"
include "df-ne.mm"
include "cvsca.mm"
include "cv1.mm"
include "eqid.mm"
include "simpll1.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "simpll3.mm"
include "fveq2.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccv.mm"
include "fta1blem.mm"
include "expr.mm"
include "syl5bir.mm"
include "orrd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "isdomn.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem fta1b
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume fta1b.p: |- P = ( Poly1 ` R )
  assume fta1b.b: |- B = ( Base ` P )
  assume fta1b.d: |- D = ( deg1 ` R )
  assume fta1b.o: |- O = ( eval1 ` R )
  assume fta1b.w: |- W = ( 0g ` R )
  assume fta1b.z: |- .0. = ( 0g ` P )

  disjoint B f
  disjoint D f
  disjoint O f
  disjoint R f
  disjoint W f
  disjoint P f
  disjoint .0. f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  disjoint O x
  disjoint O y
  disjoint R x
  disjoint R y
  disjoint W x
  disjoint W y
  disjoint .0. x
  disjoint .0. y
  assert |- ( R e. IDomn <-> ( R e. CRing /\ R e. NzRing /\ A. f e. ( B \ { .0. } ) ( # ` ( `' ( O ` f ) " { W } ) ) <_ ( D ` f ) ) )

  proof
    cR
    cidom
    wcel
    #
    cR
    ccrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    vf
    cv
    #
    cO
    cfv
    #
    ccnv
    #
    cW
    csn
    #
    cima
    #
    chash
    cfv
    #
    @3
    cD
    cfv
    #
    cle
    wbr
    #
    vf
    cB
    c.0
    csn
    cdif
    #
    wral
    #
    w3a
    #
    @0
    @1
    @2
    @12
    @0
    @1
    cR
    cdomn
    wcel
    #
    cR
    isidom
    #
    simplbi
    @0
    @14
    @2
    @0
    @1
    @14
    @15
    simprbi
    cR
    domnnzr
    syl
    @0
    @10
    vf
    @11
    @0
    @3
    @11
    wcel
    #
    wa
    cB
    cD
    cP
    cR
    @3
    cO
    cW
    c.0
    fta1b.p
    fta1b.b
    fta1b.d
    fta1b.o
    fta1b.w
    fta1b.z
    @0
    @16
    simpl
    @16
    @3
    cB
    wcel
    #
    @0
    @16
    @17
    @3
    c.0
    wne
    #
    @3
    cB
    c.0
    eldifsn
    #
    simplbi
    adantl
    @16
    @18
    @0
    @16
    @17
    @18
    @19
    simprbi
    adantl
    fta1g
    ralrimiva
    3jca
    @13
    @1
    @14
    @0
    @1
    @2
    @12
    simp1
    @13
    @2
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cW
    wceq
    #
    @20
    cW
    wceq
    #
    @21
    cW
    wceq
    #
    wo
    #
    wi
    #
    vy
    cR
    cbs
    cfv
    #
    wral
    vx
    @28
    wral
    @14
    @1
    @2
    @12
    simp2
    @13
    @27
    vx
    vy
    @28
    @28
    @13
    @20
    @28
    wcel
    #
    @21
    @28
    wcel
    #
    wa
    #
    wa
    #
    @23
    @26
    @32
    @23
    wa
    #
    @24
    @25
    @24
    wn
    @20
    cW
    wne
    #
    @33
    @25
    @20
    cW
    df-ne
    @32
    @23
    @34
    @25
    @32
    @23
    @34
    wa
    #
    wa
    #
    cB
    cD
    cP
    cR
    cP
    cvsca
    cfv
    #
    @22
    @28
    @20
    @21
    cO
    cW
    cR
    cv1
    cfv
    #
    c.0
    fta1b.p
    fta1b.b
    fta1b.d
    fta1b.o
    fta1b.w
    fta1b.z
    @28
    eqid
    #
    @22
    eqid
    #
    @38
    eqid
    @37
    eqid
    @1
    @2
    @12
    @31
    @35
    simpll1
    @13
    @29
    @30
    @35
    simplrl
    @13
    @29
    @30
    @35
    simplrr
    @32
    @23
    @34
    simprl
    @32
    @23
    @34
    simprr
    @36
    @12
    @20
    @38
    @37
    co
    #
    @11
    wcel
    @41
    cO
    cfv
    #
    ccnv
    #
    @6
    cima
    #
    chash
    cfv
    #
    @41
    cD
    cfv
    #
    cle
    wbr
    #
    wi
    @1
    @2
    @12
    @31
    @35
    simpll3
    @10
    @47
    vf
    @41
    @11
    @3
    @41
    wceq
    #
    @8
    @45
    @9
    @46
    cle
    @48
    @7
    @44
    chash
    @48
    @5
    @43
    @6
    @48
    @4
    @42
    @3
    @41
    cO
    fveq2
    cnveqd
    imaeq1d
    fveq2d
    @3
    @41
    cD
    fveq2
    breq12d
    rspccv
    syl
    fta1blem
    expr
    syl5bir
    orrd
    ex
    ralrimivva
    vx
    vy
    @28
    cR
    @22
    cW
    @39
    @40
    fta1b.w
    isdomn
    sylanbrc
    @15
    sylanbrc
    impbii
end
