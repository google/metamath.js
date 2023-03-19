include "cin.mm"
include "ccom.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "trrelssd.mm"
include "inss2.mm"
include "ssind.mm"
include "coeq12d.mm"
include "3sstr4d.mm"

theorem trrelind
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  assume trrelind.r: |- ( ph -> ( R o. R ) C_ R )
  assume trrelind.s: |- ( ph -> ( S o. S ) C_ S )
  assume trrelind.t: |- ( ph -> T = ( R i^i S ) )


  assert |- ( ph -> ( T o. T ) C_ T )

  proof
    wph
    cR
    cS
    cin
    #
    @0
    ccom
    #
    @0
    cT
    cT
    ccom
    cT
    wph
    @1
    cR
    cS
    wph
    cR
    @0
    @0
    trrelind.r
    @0
    cR
    wss
    wph
    cR
    cS
    inss1
    a1i
    #
    @2
    trrelssd
    wph
    cS
    @0
    @0
    trrelind.s
    @0
    cS
    wss
    wph
    cR
    cS
    inss2
    a1i
    #
    @3
    trrelssd
    ssind
    wph
    cT
    @0
    cT
    @0
    trrelind.t
    trrelind.t
    coeq12d
    trrelind.t
    3sstr4d
end
