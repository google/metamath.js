include "cn0.mm"
include "wcel.mm"
include "czn.mm"
include "cfv.mm"
include "cnx.mm"
include "cple.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "zring.mm"
include "cv.mm"
include "csn.mm"
include "crsp.mm"
include "cqg.mm"
include "cqus.mm"
include "czrh.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cfzo.mm"
include "cif.mm"
include "cres.mm"
include "cle.mm"
include "ccom.mm"
include "ccnv.mm"
include "csb.mm"
include "crg.mm"
include "zringring.mm"
include "a1i.mm"
include "wa.mm"
include "cvv.mm"
include "ovexd.mm"
include "id.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "sneqd.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "sylan9eqr.mm"
include "fvex.mm"
include "resex.mm"
include "simpll.mm"
include "eqeq1d.mm"
include "oveq2d.mm"
include "ifbieq2d.mm"
include "reseq12d.mm"
include "coeq1d.mm"
include "cnveqd.mm"
include "coeq12d.mm"
include "csbied.mm"
include "opeq2d.mm"
include "df-zn.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem znval
  let cS: class S
  let cU: class U
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  assume znval.s: |- S = ( RSpan ` ZZring )
  assume znval.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )
  assume znval.y: |- Y = ( Z/nZ ` N )
  assume znval.f: |- F = ( ( ZRHom ` U ) |` W )
  assume znval.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znval.l: |- .<_ = ( ( F o. <_ ) o. `' F )


  assert |- ( N e. NN0 -> Y = ( U sSet <. ( le ` ndx ) , .<_ >. ) )

  proof
    cN
    cn0
    wcel
    cY
    cN
    czn
    cfv
    cU
    cnx
    cple
    cfv
    #
    c.le
    cop
    #
    csts
    co
    #
    znval.y
    vn
    cN
    vz
    zring
    vs
    vz
    cv
    #
    @3
    vn
    cv
    #
    csn
    #
    @3
    crsp
    cfv
    #
    cfv
    #
    cqg
    co
    #
    cqus
    co
    #
    vs
    cv
    #
    @0
    vf
    @10
    czrh
    cfv
    #
    @4
    cc0
    wceq
    #
    cz
    cc0
    @4
    cfzo
    co
    #
    cif
    #
    cres
    #
    vf
    cv
    #
    cle
    ccom
    #
    @16
    ccnv
    #
    ccom
    #
    csb
    #
    cop
    #
    csts
    co
    #
    csb
    #
    csb
    @2
    cn0
    czn
    @4
    cN
    wceq
    #
    vz
    zring
    @23
    @2
    crg
    zring
    crg
    wcel
    @24
    zringring
    a1i
    @24
    @3
    zring
    wceq
    #
    wa
    #
    vs
    @9
    @22
    @2
    cvv
    @26
    @3
    @8
    cqus
    ovexd
    @26
    @10
    @9
    wceq
    #
    wa
    #
    @10
    cU
    @21
    @1
    csts
    @27
    @26
    @10
    @9
    cU
    @27
    id
    @26
    @9
    zring
    zring
    cN
    csn
    #
    cS
    cfv
    #
    cqg
    co
    #
    cqus
    co
    cU
    @26
    @3
    zring
    @8
    @31
    cqus
    @24
    @25
    simpr
    #
    @26
    @3
    zring
    @7
    @30
    cqg
    @32
    @26
    @5
    @29
    @6
    cS
    @26
    @6
    zring
    crsp
    cfv
    cS
    @26
    @3
    zring
    crsp
    @32
    fveq2d
    znval.s
    syl6eqr
    @26
    @4
    cN
    @24
    @25
    simpl
    sneqd
    fveq12d
    oveq12d
    oveq12d
    znval.u
    syl6eqr
    sylan9eqr
    #
    @28
    @20
    c.le
    @0
    @28
    vf
    @15
    @19
    c.le
    cvv
    @15
    cvv
    wcel
    @28
    @11
    @14
    @10
    czrh
    fvex
    resex
    a1i
    @28
    @16
    @15
    wceq
    #
    wa
    #
    @19
    cF
    cle
    ccom
    #
    cF
    ccnv
    #
    ccom
    c.le
    @35
    @17
    @36
    @18
    @37
    @35
    @16
    cF
    cle
    @34
    @28
    @16
    @15
    cF
    @34
    id
    @28
    @15
    cU
    czrh
    cfv
    #
    cW
    cres
    cF
    @28
    @11
    @38
    @14
    cW
    @28
    @10
    cU
    czrh
    @33
    fveq2d
    @28
    @14
    cN
    cc0
    wceq
    #
    cz
    cc0
    cN
    cfzo
    co
    #
    cif
    cW
    @28
    @12
    @39
    @13
    @40
    cz
    @28
    @4
    cN
    cc0
    @24
    @25
    @27
    simpll
    #
    eqeq1d
    @28
    @4
    cN
    cc0
    cfzo
    @41
    oveq2d
    ifbieq2d
    znval.w
    syl6eqr
    reseq12d
    znval.f
    syl6eqr
    sylan9eqr
    #
    coeq1d
    @35
    @16
    cF
    @42
    cnveqd
    coeq12d
    znval.l
    syl6eqr
    csbied
    opeq2d
    oveq12d
    csbied
    csbied
    vz
    vf
    vn
    vs
    df-zn
    cU
    @1
    csts
    ovex
    fvmpt
    syl5eq
end
