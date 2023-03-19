include "wnfc.mm"
include "wnf.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "pm3.2i.mm"
include "ax-gen.mm"
include "vtoclgft.mm"
include "mp3an12.mm"

theorem bj-vtoclgfALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-vtoclgfALT.1: |- F/_ x A
  assume bj-vtoclgfALT.2: |- F/ x ps
  assume bj-vtoclgfALT.3: |- ( x = A -> ( ph <-> ps ) )
  assume bj-vtoclgfALT.4: |- ph


  assert |- ( A e. V -> ps )

  proof
    vx
    cA
    wnfc
    #
    wps
    vx
    wnf
    #
    wa
    vx
    cv
    cA
    wceq
    wph
    wps
    wb
    wi
    #
    vx
    wal
    #
    wph
    vx
    wal
    #
    wa
    cA
    cV
    wcel
    wps
    @0
    @1
    bj-vtoclgfALT.1
    bj-vtoclgfALT.2
    pm3.2i
    @3
    @4
    @2
    vx
    bj-vtoclgfALT.3
    ax-gen
    wph
    vx
    bj-vtoclgfALT.4
    ax-gen
    pm3.2i
    wph
    wps
    vx
    cA
    cV
    vtoclgft
    mp3an12
end
