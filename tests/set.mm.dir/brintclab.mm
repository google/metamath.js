include "cab.mm"
include "cint.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "df-br.mm"
include "opex.mm"
include "elintab.mm"
include "bitri.mm"

theorem brintclab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A |^| { x | ph } B <-> A. x ( ph -> <. A , B >. e. x ) )

  proof
    cA
    cB
    wph
    vx
    cab
    cint
    #
    wbr
    cA
    cB
    cop
    #
    @0
    wcel
    wph
    @1
    vx
    cv
    wcel
    wi
    vx
    wal
    cA
    cB
    @0
    df-br
    wph
    vx
    @1
    cA
    cB
    opex
    elintab
    bitri
end
