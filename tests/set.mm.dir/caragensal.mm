include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "caragen0.mm"
include "wa.mm"
include "come.mm"
include "adantr.mm"
include "simpr.mm"
include "caragendifcl.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "wss.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "caragenunicl.mm"
include "ex.mm"
include "3jca.mm"
include "cvv.mm"
include "wb.mm"
include "ccaragen.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "issal.mm"
include "syl.mm"
include "mpbird.mm"

theorem caragensal
  let wph: wff ph
  let cS: class S
  let cO: class O
  let vx: setvar x
  let vk: setvar k
  assume caragensal.o: |- ( ph -> O e. OutMeas )
  assume caragensal.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> S e. SAlg )

  proof
    wph
    cS
    csalg
    wcel
    #
    c0
    cS
    wcel
    #
    cS
    cuni
    vx
    cv
    #
    cdif
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @2
    com
    cdom
    wbr
    #
    @2
    cuni
    cS
    wcel
    #
    wi
    #
    vx
    cS
    cpw
    #
    wral
    #
    w3a
    #
    wph
    @1
    @4
    @9
    wph
    cS
    cO
    caragensal.o
    caragensal.s
    caragen0
    wph
    @3
    vx
    cS
    wph
    @2
    cS
    wcel
    #
    wa
    cS
    @2
    cO
    wph
    cO
    come
    wcel
    #
    @11
    caragensal.o
    adantr
    caragensal.s
    wph
    @11
    simpr
    caragendifcl
    ralrimiva
    wph
    @7
    vx
    @8
    wph
    @2
    @8
    wcel
    #
    wa
    #
    @5
    @6
    @14
    @5
    wa
    cS
    cO
    @2
    wph
    @12
    @13
    @5
    caragensal.o
    ad2antrr
    caragensal.s
    @13
    @2
    cS
    wss
    wph
    @5
    @2
    cS
    elpwi
    ad2antlr
    @14
    @5
    simpr
    caragenunicl
    ex
    ralrimiva
    3jca
    wph
    cS
    cvv
    wcel
    #
    @0
    @10
    wb
    @15
    wph
    cS
    cO
    ccaragen
    cfv
    cvv
    caragensal.s
    cO
    ccaragen
    fvex
    eqeltri
    a1i
    vx
    cS
    cvv
    issal
    syl
    mpbird
end
