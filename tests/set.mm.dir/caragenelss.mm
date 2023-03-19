include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cdm.mm"
include "cuni.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "caragenel.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqcomi.mm"
include "pweqi.mm"
include "a1i.mm"
include "eleqtrd.mm"
include "wb.mm"
include "elpwg.mm"
include "syl.mm"

theorem caragenelss
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume caragenelss.o: |- ( ph -> O e. OutMeas )
  assume caragenelss.s: |- S = ( CaraGen ` O )
  assume caragenelss.a: |- ( ph -> A e. S )
  assume caragenelss.x: |- X = U. dom O


  assert |- ( ph -> A C_ X )

  proof
    wph
    cA
    cX
    cpw
    #
    wcel
    #
    cA
    cX
    wss
    #
    wph
    cA
    cO
    cdm
    cuni
    #
    cpw
    #
    @0
    wph
    cA
    @4
    wcel
    #
    vx
    cv
    #
    cA
    cin
    cO
    cfv
    @6
    cA
    cdif
    cO
    cfv
    cxad
    co
    @6
    cO
    cfv
    wceq
    vx
    @4
    wral
    #
    wph
    cA
    cS
    wcel
    #
    @5
    @7
    wa
    caragenelss.a
    wph
    cS
    cA
    cO
    vx
    caragenelss.o
    caragenelss.s
    caragenel
    mpbid
    simpld
    @4
    @0
    wceq
    wph
    @3
    cX
    cX
    @3
    caragenelss.x
    eqcomi
    pweqi
    a1i
    eleqtrd
    wph
    @8
    @1
    @2
    wb
    caragenelss.a
    cA
    cX
    cS
    elpwg
    syl
    mpbid
end
