include "con0.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cep.mm"
include "cpred.mm"
include "wcel.mm"
include "predon.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "ralbiia.mm"
include "epweon.mm"
include "epse.mm"
include "crecs.mm"
include "cwrecs.mm"
include "df-recs.mm"
include "eqtri.mm"
include "wfr3.mm"
include "sylan2br.mm"
include "eqcomd.mm"

theorem tfr3ALT
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cG: class G
  assume tfrALT.1: |- F = recs ( G )

  disjoint B x
  disjoint G x
  disjoint F x
  assert |- ( ( B Fn On /\ A. x e. On ( B ` x ) = ( G ` ( B |` x ) ) ) -> B = F )

  proof
    cB
    con0
    wfn
    #
    vx
    cv
    #
    cB
    cfv
    #
    cB
    @1
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vx
    con0
    wral
    #
    wa
    cF
    cB
    @6
    @0
    @2
    cB
    con0
    cep
    @1
    cpred
    #
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vx
    con0
    wral
    cF
    cB
    wceq
    @10
    @5
    vx
    con0
    @1
    con0
    wcel
    #
    @9
    @4
    @2
    @11
    @8
    @3
    cG
    @11
    @7
    @1
    cB
    @1
    predon
    reseq2d
    fveq2d
    eqeq2d
    ralbiia
    vx
    con0
    cep
    cF
    cG
    cB
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
    wfr3
    sylan2br
    eqcomd
end
