include "cvv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "abrexexg.mm"
include "syl.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "ex.mm"
include "alrimiv.mm"
include "ssab.mm"
include "sylibr.mm"
include "ssexd.mm"
include "wdom2d.mm"

theorem wdomd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  assume wdomd.b: |- ( ph -> B e. W )
  assume wdomd.o: |- ( ( ph /\ x e. A ) -> E. y e. B x = X )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint X x
  assert |- ( ph -> A ~<_* B )

  proof
    wph
    vx
    vy
    cA
    cB
    cvv
    cW
    cX
    wph
    cA
    vx
    cv
    #
    cX
    wceq
    vy
    cB
    wrex
    #
    vx
    cab
    #
    cvv
    wph
    cB
    cW
    wcel
    @2
    cvv
    wcel
    wdomd.b
    vy
    vx
    cB
    cX
    cW
    abrexexg
    syl
    wph
    @0
    cA
    wcel
    #
    @1
    wi
    #
    vx
    wal
    cA
    @2
    wss
    wph
    @4
    vx
    wph
    @3
    @1
    wdomd.o
    ex
    alrimiv
    @1
    vx
    cA
    ssab
    sylibr
    ssexd
    wdomd.b
    wdomd.o
    wdom2d
end
