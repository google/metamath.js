include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "weq.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "imbi1d.mm"
include "wex.mm"
include "19.8a.mm"
include "mo2v.mm"
include "sylibr.mm"
include "vtoclg.mm"
include "wn.mm"
include "eqvisset.mm"
include "imim2i.mm"
include "con3rr3.mm"
include "alimdv.mm"
include "alnex.mm"
include "exmo.mm"
include "ori.mm"
include "sylbi.mm"
include "syl6.mm"
include "pm2.61i.mm"

theorem mo2icl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A. x ( ph -> x = A ) -> E* x ph )

  proof
    cA
    cvv
    wcel
    #
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    wmo
    #
    wi
    #
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    @5
    wi
    @6
    vy
    cA
    cvv
    vy
    cv
    #
    cA
    wceq
    #
    @9
    @4
    @5
    @11
    @8
    @3
    vx
    @11
    @7
    @2
    wph
    @10
    cA
    @1
    eqeq2
    imbi2d
    albidv
    imbi1d
    @9
    @9
    vy
    wex
    @5
    @9
    vy
    19.8a
    wph
    vx
    vy
    mo2v
    sylibr
    vtoclg
    @0
    wn
    #
    @4
    wph
    wn
    #
    vx
    wal
    #
    @5
    @12
    @3
    @13
    vx
    @3
    wph
    @0
    @2
    @0
    wph
    vx
    cA
    eqvisset
    imim2i
    con3rr3
    alimdv
    @14
    wph
    vx
    wex
    #
    wn
    @5
    wph
    vx
    alnex
    @15
    @5
    wph
    vx
    exmo
    ori
    sylbi
    syl6
    pm2.61i
end
