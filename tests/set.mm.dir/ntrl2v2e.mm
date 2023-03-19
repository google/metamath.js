include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "wn.mm"
include "cc0.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "w3a.mm"
include "wne.mm"
include "0z.mm"
include "1z.mm"
include "3pm3.2i.mm"
include "0ne1.mm"
include "cs2.mm"
include "cop.mm"
include "cpr.mm"
include "wceq.mm"
include "s2prop.mm"
include "mp2an.mm"
include "eqtri.mm"
include "fpropnf1.mm"
include "simpri.mm"
include "intnan.mm"
include "istrl.mm"
include "mtbir.mm"

theorem ntrl2v2e
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume wlk2v2e.i: |- I = <" { X , Y } ">
  assume wlk2v2e.f: |- F = <" 0 0 ">
  assume wlk2v2e.x: |- X e. _V
  assume wlk2v2e.y: |- Y e. _V
  assume wlk2v2e.p: |- P = <" X Y X ">
  assume wlk2v2e.g: |- G = <. { X , Y } , I >.


  assert |- -. F ( Trails ` G ) P

  proof
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    ccnv
    wfun
    #
    wa
    @1
    @0
    cF
    wfun
    #
    @1
    wn
    #
    cc0
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @4
    w3a
    cc0
    c1
    wne
    @2
    @3
    wa
    @4
    @5
    @4
    0z
    1z
    0z
    3pm3.2i
    0ne1
    cz
    cF
    cz
    cz
    cc0
    c1
    cc0
    cF
    cc0
    cc0
    cs2
    #
    cc0
    cc0
    cop
    c1
    cc0
    cop
    cpr
    #
    wlk2v2e.f
    @4
    @4
    @6
    @7
    wceq
    0z
    0z
    cc0
    cc0
    cz
    s2prop
    mp2an
    eqtri
    fpropnf1
    mp2an
    simpri
    intnan
    cP
    cF
    cG
    istrl
    mtbir
end
