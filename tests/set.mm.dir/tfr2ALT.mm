include "con0.mm"
include "wcel.mm"
include "cfv.mm"
include "cep.mm"
include "cpred.mm"
include "cres.mm"
include "epweon.mm"
include "epse.mm"
include "crecs.mm"
include "cwrecs.mm"
include "df-recs.mm"
include "eqtri.mm"
include "wfr2.mm"
include "predon.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem tfr2ALT
  let cA: class A
  let cF: class F
  let cG: class G
  assume tfrALT.1: |- F = recs ( G )


  assert |- ( A e. On -> ( F ` A ) = ( G ` ( F |` A ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cF
    cfv
    cF
    con0
    cep
    cA
    cpred
    #
    cres
    #
    cG
    cfv
    cF
    cA
    cres
    #
    cG
    cfv
    con0
    cep
    cF
    cG
    cA
    epweon
    con0
    epse
    cF
    cG
    crecs
    con0
    cep
    cG
    cwrecs
    tfrALT.1
    cG
    df-recs
    eqtri
    wfr2
    @0
    @2
    @3
    cG
    @0
    @1
    cA
    cF
    cA
    predon
    reseq2d
    fveq2d
    eqtrd
end
