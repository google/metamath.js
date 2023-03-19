include "cab.mm"
include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "elint.mm"
include "nfsab1.mm"
include "nfv.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "abid.mm"
include "syl6bb.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "cbval.mm"
include "bitri.mm"

theorem elintab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume inteqab.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph y
  assert |- ( A e. |^| { x | ph } <-> A. x ( ph -> A e. x ) )

  proof
    cA
    wph
    vx
    cab
    #
    cint
    wcel
    vy
    cv
    #
    @0
    wcel
    #
    cA
    @1
    wcel
    #
    wi
    #
    vy
    wal
    wph
    cA
    vx
    cv
    #
    wcel
    #
    wi
    #
    vx
    wal
    vy
    cA
    @0
    inteqab.1
    elint
    @4
    @7
    vy
    vx
    @2
    @3
    vx
    wph
    vx
    vy
    nfsab1
    @3
    vx
    nfv
    nfim
    @7
    vy
    nfv
    vy
    vx
    weq
    #
    @2
    wph
    @3
    @6
    @8
    @2
    @5
    @0
    wcel
    wph
    @1
    @5
    @0
    eleq1
    wph
    vx
    abid
    syl6bb
    @1
    @5
    cA
    eleq2
    imbi12d
    cbval
    bitri
end
