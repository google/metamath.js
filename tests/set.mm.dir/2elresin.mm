include "wfn.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "cin.mm"
include "cres.mm"
include "wi.mm"
include "fnop.mm"
include "anim12i.mm"
include "an4s.mm"
include "elin.mm"
include "sylibr.mm"
include "vex.mm"
include "opres.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "syl.mm"
include "ex.mm"
include "pm2.43d.mm"
include "resss.mm"
include "sseli.mm"
include "impbid1.mm"

theorem 2elresin
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F Fn A /\ G Fn B ) -> ( ( <. x , y >. e. F /\ <. x , z >. e. G ) <-> ( <. x , y >. e. ( F |` ( A i^i B ) ) /\ <. x , z >. e. ( G |` ( A i^i B ) ) ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @3
    vz
    cv
    #
    cop
    #
    cG
    wcel
    #
    wa
    #
    @5
    cF
    cA
    cB
    cin
    #
    cres
    #
    wcel
    #
    @8
    cG
    @11
    cres
    #
    wcel
    #
    wa
    #
    @2
    @10
    @16
    @2
    @10
    @10
    @16
    wi
    #
    @2
    @10
    wa
    #
    @3
    @11
    wcel
    #
    @17
    @18
    @3
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    @19
    @0
    @6
    @1
    @9
    @22
    @0
    @6
    wa
    @20
    @1
    @9
    wa
    @21
    cA
    @3
    @4
    cF
    fnop
    cB
    @3
    @7
    cG
    fnop
    anim12i
    an4s
    @3
    cA
    cB
    elin
    sylibr
    @19
    @16
    @10
    @19
    @13
    @6
    @15
    @9
    @3
    @4
    cF
    @11
    vy
    vex
    opres
    @3
    @7
    cG
    @11
    vz
    vex
    opres
    anbi12d
    biimprd
    syl
    ex
    pm2.43d
    @13
    @6
    @15
    @9
    @12
    cF
    @5
    cF
    @11
    resss
    sseli
    @14
    cG
    @8
    cG
    @11
    resss
    sseli
    anim12i
    impbid1
end
