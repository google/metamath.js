include "wfun.mm"
include "wa.mm"
include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "eqfunresadj.mm"
include "df-suc.mm"
include "reseq2i.mm"
include "3eqtr4g.mm"

theorem eqfunressuc
  let cF: class F
  let cG: class G
  let cX: class X


  assert |- ( ( ( Fun F /\ Fun G ) /\ ( F |` X ) = ( G |` X ) /\ ( X e. dom F /\ X e. dom G /\ ( F ` X ) = ( G ` X ) ) ) -> ( F |` suc X ) = ( G |` suc X ) )

  proof
    cF
    wfun
    cG
    wfun
    wa
    cF
    cX
    cres
    cG
    cX
    cres
    wceq
    cX
    cF
    cdm
    wcel
    cX
    cG
    cdm
    wcel
    cX
    cF
    cfv
    cX
    cG
    cfv
    wceq
    w3a
    w3a
    cF
    cX
    cX
    csn
    cun
    #
    cres
    cG
    @0
    cres
    cF
    cX
    csuc
    #
    cres
    cG
    @1
    cres
    cF
    cG
    cX
    cX
    eqfunresadj
    @1
    @0
    cF
    cX
    df-suc
    #
    reseq2i
    @1
    @0
    cG
    @2
    reseq2i
    3eqtr4g
end
