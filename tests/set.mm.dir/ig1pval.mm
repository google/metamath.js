include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cin.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "cig1p.mm"
include "cvv.mm"
include "elex.mm"
include "cpl1.mm"
include "clidl.mm"
include "c0g.mm"
include "cdg1.mm"
include "cmn1.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eqeq2d.mm"
include "ineq2d.mm"
include "fveq1d.mm"
include "difeq2d.mm"
include "imaeq12d.mm"
include "infeq1d.mm"
include "eqeq12d.mm"
include "riotaeqbidv.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "df-ig1p.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"
include "eqeq1.mm"
include "ineq1.mm"
include "difeq1.mm"
include "imaeq2d.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "riotaex.mm"
include "ifex.mm"
include "sylan9eq.mm"

theorem ig1pval
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let vg: setvar g
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pval.z: |- .0. = ( 0g ` P )
  assume ig1pval.u: |- U = ( LIdeal ` P )
  assume ig1pval.d: |- D = ( deg1 ` R )
  assume ig1pval.m: |- M = ( Monic1p ` R )

  disjoint I g
  disjoint M g
  disjoint R g
  disjoint D i
  disjoint D r
  disjoint i r
  disjoint I i
  disjoint g i
  disjoint M i
  disjoint M r
  disjoint g r
  disjoint R i
  disjoint R r
  disjoint U i
  disjoint U r
  disjoint .0. i
  disjoint .0. r
  assert |- ( ( R e. V /\ I e. U ) -> ( G ` I ) = if ( I = { .0. } , .0. , ( iota_ g e. ( I i^i M ) ( D ` g ) = inf ( ( D " ( I \ { .0. } ) ) , RR , < ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cU
    wcel
    cI
    cG
    cfv
    cI
    vi
    cU
    vi
    cv
    #
    c.0
    csn
    #
    wceq
    #
    c.0
    vg
    cv
    #
    cD
    cfv
    #
    cD
    @1
    @2
    cdif
    #
    cima
    #
    cr
    clt
    cinf
    #
    wceq
    #
    vg
    @1
    cM
    cin
    #
    crio
    #
    cif
    #
    cmpt
    #
    cfv
    cI
    @2
    wceq
    #
    c.0
    @5
    cD
    cI
    @2
    cdif
    #
    cima
    #
    cr
    clt
    cinf
    #
    wceq
    #
    vg
    cI
    cM
    cin
    #
    crio
    #
    cif
    #
    @0
    cI
    cG
    @13
    @0
    cG
    cR
    cig1p
    cfv
    #
    @13
    ig1pval.g
    @0
    cR
    cvv
    wcel
    @22
    @13
    wceq
    cR
    cV
    elex
    vr
    cR
    vi
    vr
    cv
    #
    cpl1
    cfv
    #
    clidl
    cfv
    #
    @1
    @24
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @26
    @4
    @23
    cdg1
    cfv
    #
    cfv
    #
    @29
    @1
    @27
    cdif
    #
    cima
    #
    cr
    clt
    cinf
    #
    wceq
    #
    vg
    @1
    @23
    cmn1
    cfv
    #
    cin
    #
    crio
    #
    cif
    #
    cmpt
    @13
    cvv
    cig1p
    @23
    cR
    wceq
    #
    vi
    @25
    @38
    cU
    @12
    @39
    @25
    cP
    clidl
    cfv
    #
    cU
    @39
    @24
    cP
    clidl
    @39
    @24
    cR
    cpl1
    cfv
    cP
    @23
    cR
    cpl1
    fveq2
    ig1pval.p
    syl6eqr
    #
    fveq2d
    ig1pval.u
    syl6eqr
    @39
    @28
    @3
    @26
    @37
    c.0
    @11
    @39
    @27
    @2
    @1
    @39
    @26
    c.0
    @39
    @26
    cP
    c0g
    cfv
    #
    c.0
    @39
    @24
    cP
    c0g
    @41
    fveq2d
    ig1pval.z
    syl6eqr
    #
    sneqd
    #
    eqeq2d
    @43
    @39
    @34
    @9
    vg
    @36
    @10
    @39
    @35
    cM
    @1
    @39
    @35
    cR
    cmn1
    cfv
    cM
    @23
    cR
    cmn1
    fveq2
    ig1pval.m
    syl6eqr
    ineq2d
    @39
    @30
    @5
    @33
    @8
    @39
    @4
    @29
    cD
    @39
    @29
    cR
    cdg1
    cfv
    cD
    @23
    cR
    cdg1
    fveq2
    ig1pval.d
    syl6eqr
    #
    fveq1d
    @39
    cr
    @32
    @7
    clt
    @39
    @29
    cD
    @31
    @6
    @45
    @39
    @27
    @2
    @1
    @44
    difeq2d
    imaeq12d
    infeq1d
    eqeq12d
    riotaeqbidv
    ifbieq12d
    mpteq12dv
    vg
    vi
    vr
    df-ig1p
    vi
    cU
    @12
    cU
    @40
    cvv
    ig1pval.u
    cP
    clidl
    fvex
    eqeltri
    mptex
    fvmpt
    syl
    syl5eq
    fveq1d
    vi
    cI
    @12
    @21
    cU
    @13
    @1
    cI
    wceq
    #
    @3
    @14
    @11
    @20
    c.0
    @1
    cI
    @2
    eqeq1
    @46
    @9
    @18
    vg
    @10
    @19
    @1
    cI
    cM
    ineq1
    @46
    @8
    @17
    @5
    @46
    cr
    @7
    @16
    clt
    @46
    @6
    @15
    cD
    @1
    cI
    @2
    difeq1
    imaeq2d
    infeq1d
    eqeq2d
    riotaeqbidv
    ifbieq2d
    @13
    eqid
    @14
    c.0
    @20
    c.0
    @42
    cvv
    ig1pval.z
    cP
    c0g
    fvex
    eqeltri
    @18
    vg
    @19
    riotaex
    ifex
    fvmpt
    sylan9eq
end
