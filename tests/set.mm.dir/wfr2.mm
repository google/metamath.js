include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "wfrlem16.mm"
include "eleq2i.mm"
include "wfr2a.mm"
include "sylbir.mm"

theorem wfr2
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume wfr2.1: |- R We A
  assume wfr2.2: |- R Se A
  assume wfr2.3: |- F = wrecs ( R , A , G )


  assert |- ( X e. A -> ( F ` X ) = ( G ` ( F |` Pred ( R , A , X ) ) ) )

  proof
    cX
    cA
    wcel
    cX
    cF
    cdm
    #
    wcel
    cX
    cF
    cfv
    cF
    cA
    cR
    cX
    cpred
    cres
    cG
    cfv
    wceq
    @0
    cA
    cX
    vx
    cA
    cF
    vx
    cv
    #
    cF
    cA
    cR
    @1
    cpred
    cres
    cG
    cfv
    cop
    csn
    cun
    #
    cR
    cF
    cG
    wfr2.1
    wfr2.2
    wfr2.3
    @2
    eqid
    wfrlem16
    eleq2i
    cA
    cR
    cF
    cG
    cX
    wfr2.1
    wfr2.2
    wfr2.3
    wfr2a
    sylbir
end
