include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "sp.mm"
include "impcom.mm"
include "sylan2b.mm"
include "syl2anc.mm"

theorem bnj1294
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1294.1: |- ( ph -> A. x e. A ps )
  assume bnj1294.2: |- ( ph -> x e. A )


  assert |- ( ph -> ps )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    vx
    cA
    wral
    #
    wps
    bnj1294.2
    bnj1294.1
    @1
    @0
    @0
    wps
    wi
    #
    vx
    wal
    #
    wps
    wps
    vx
    cA
    df-ral
    @3
    @0
    wps
    @2
    vx
    sp
    impcom
    sylan2b
    syl2anc
end
