include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cres.mm"
include "cof.mm"
include "wceq.mm"
include "inss2.mm"
include "sseli.mm"
include "fvres.mm"
include "oveq12d.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "inindi.mm"
include "incom.mm"
include "dmres.mm"
include "ineq12i.mm"
include "3eqtr4ri.mm"
include "eqid.mm"
include "mpteq12i.mm"
include "resmpt3.mm"
include "offval3.mm"
include "reseq1d.mm"
include "cvv.mm"
include "resexg.mm"
include "syl2an.mm"
include "3eqtr4a.mm"

theorem offres
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  let va: setvar a
  let vb: setvar b


  assert |- ( ( F e. V /\ G e. W ) -> ( ( F oF R G ) |` D ) = ( ( F |` D ) oF R ( G |` D ) ) )

  proof
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    #
    vx
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cD
    cres
    #
    vx
    cF
    cD
    cres
    #
    cdm
    #
    cG
    cD
    cres
    #
    cdm
    #
    cin
    #
    @6
    @12
    cfv
    #
    @6
    @14
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cF
    cG
    cR
    cof
    #
    co
    #
    cD
    cres
    @12
    @14
    @21
    co
    #
    vx
    @5
    cD
    cin
    #
    @19
    cmpt
    vx
    @24
    @9
    cmpt
    @20
    @11
    vx
    @24
    @19
    @9
    @6
    @24
    wcel
    @6
    cD
    wcel
    #
    @19
    @9
    wceq
    @24
    cD
    @6
    @5
    cD
    inss2
    sseli
    @25
    @17
    @7
    @18
    @8
    cR
    @6
    cD
    cF
    fvres
    @6
    cD
    cG
    fvres
    oveq12d
    syl
    mpteq2ia
    vx
    @16
    @19
    @24
    @19
    cD
    @5
    cin
    cD
    @3
    cin
    #
    cD
    @4
    cin
    #
    cin
    @24
    @16
    cD
    @3
    @4
    inindi
    @5
    cD
    incom
    @13
    @26
    @15
    @27
    cF
    cD
    dmres
    cG
    cD
    dmres
    ineq12i
    3eqtr4ri
    @19
    eqid
    mpteq12i
    vx
    @5
    cD
    @9
    resmpt3
    3eqtr4ri
    @2
    @22
    @10
    cD
    vx
    cR
    cF
    cG
    cV
    cW
    offval3
    reseq1d
    @0
    @12
    cvv
    wcel
    @14
    cvv
    wcel
    @23
    @20
    wceq
    @1
    cF
    cD
    cV
    resexg
    cG
    cD
    cW
    resexg
    vx
    cR
    @12
    @14
    cvv
    cvv
    offval3
    syl2an
    3eqtr4a
end
