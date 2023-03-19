include "wss.mm"
include "cdif.mm"
include "wceq.mm"
include "dfss4.mm"
include "mpbi.mm"

theorem kur14lem4
  let cA: class A
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume kur14lem.j: |- J e. Top
  assume kur14lem.x: |- X = U. J
  assume kur14lem.k: |- K = ( cls ` J )
  assume kur14lem.i: |- I = ( int ` J )
  assume kur14lem.a: |- A C_ X


  assert |- ( X \ ( X \ A ) ) = A

  proof
    cA
    cX
    wss
    cX
    cX
    cA
    cdif
    cdif
    cA
    wceq
    kur14lem.a
    cA
    cX
    dfss4
    mpbi
end
