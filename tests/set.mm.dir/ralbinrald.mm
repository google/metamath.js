include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "adantl.mm"
include "rspcdv.mm"
include "wcel.mm"
include "wa.mm"
include "bicomd.mm"
include "syl.mm"
include "biimpd.mm"
include "ralrimdva.mm"
include "impbid.mm"

theorem ralbinrald
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cX: class X
  let vk: setvar k
  assume ralbinrald.1: |- ( ph -> X e. A )
  assume ralbinrald.2: |- ( x e. A -> x = X )
  assume ralbinrald.3: |- ( x = X -> ( ps <-> th ) )

  disjoint X x
  disjoint A x
  disjoint ph x
  disjoint th x
  disjoint k x
  assert |- ( ph -> ( A. x e. A ps <-> th ) )

  proof
    wph
    wps
    vx
    cA
    wral
    wth
    wph
    wps
    wth
    vx
    cX
    cA
    ralbinrald.1
    vx
    cv
    #
    cX
    wceq
    #
    wps
    wth
    wb
    wph
    ralbinrald.3
    adantl
    rspcdv
    wph
    wth
    wps
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    wth
    wps
    @2
    wth
    wps
    wb
    #
    wph
    @2
    @1
    @3
    ralbinrald.2
    @1
    wps
    wth
    ralbinrald.3
    bicomd
    syl
    adantl
    biimpd
    ralrimdva
    impbid
end
