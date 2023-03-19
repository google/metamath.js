include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "cv.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "elioc2.mm"
include "biimp3a.mm"
include "simp1d.mm"
include "3expia.mm"
include "ssrdv.mm"

theorem iocssre
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR* /\ B e. RR ) -> ( A (,] B ) C_ RR )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    vx
    cA
    cB
    cioc
    co
    #
    cr
    @0
    @1
    vx
    cv
    #
    @2
    wcel
    #
    @3
    cr
    wcel
    #
    @0
    @1
    @4
    w3a
    @5
    cA
    @3
    clt
    wbr
    #
    @3
    cB
    cle
    wbr
    #
    @0
    @1
    @4
    @5
    @6
    @7
    w3a
    cA
    cB
    @3
    elioc2
    biimp3a
    simp1d
    3expia
    ssrdv
end
