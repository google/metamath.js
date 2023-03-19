include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "wi.mm"
include "cmpt.mm"
include "a1i.mm"
include "wb.mm"
include "fveq2.mm"
include "breqd.mm"
include "adantl.mm"
include "adantll.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "simpl.mm"
include "wal.mm"
include "id.mm"
include "gen2.mm"
include "opabbrex.mm"
include "sylancr.mm"
include "fvmptd.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "br0.mm"
include "mtbiri.mm"
include "intnanrd.mm"
include "alrimivv.mm"
include "opab0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem fvmptopab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume fvmptopab.1: |- ( ( ph /\ z = Z ) -> ( ch <-> ps ) )
  assume fvmptopab.2: |- ( ph -> { <. x , y >. | x ( F ` Z ) y } e. _V )
  assume fvmptopab.3: |- M = ( z e. _V |-> { <. x , y >. | ( x ( F ` z ) y /\ ch ) } )

  disjoint F z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps z
  assert |- ( ph -> ( M ` Z ) = { <. x , y >. | ( x ( F ` Z ) y /\ ps ) } )

  proof
    cZ
    cvv
    wcel
    #
    wph
    cZ
    cM
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cZ
    cF
    cfv
    #
    wbr
    #
    wps
    wa
    #
    vx
    vy
    copab
    #
    wceq
    #
    wi
    @0
    wph
    @8
    @0
    wph
    wa
    #
    vz
    cZ
    @2
    @3
    vz
    cv
    #
    cF
    cfv
    #
    wbr
    #
    wch
    wa
    #
    vx
    vy
    copab
    #
    @7
    cvv
    cM
    cvv
    cM
    vz
    cvv
    @14
    cmpt
    wceq
    @9
    fvmptopab.3
    a1i
    @9
    @10
    cZ
    wceq
    #
    wa
    #
    @13
    @6
    vx
    vy
    @16
    @12
    @5
    wch
    wps
    @15
    @12
    @5
    wb
    @9
    @15
    @11
    @4
    @2
    @3
    @10
    cZ
    cF
    fveq2
    breqd
    adantl
    wph
    @15
    wch
    wps
    wb
    @0
    fvmptopab.1
    adantll
    anbi12d
    opabbidv
    @0
    wph
    simpl
    @9
    @5
    @5
    wi
    #
    vy
    wal
    vx
    wal
    @5
    vx
    vy
    copab
    cvv
    wcel
    #
    @7
    cvv
    wcel
    @17
    vx
    vy
    @5
    id
    gen2
    wph
    @18
    @0
    fvmptopab.2
    adantl
    @5
    wps
    vx
    vy
    @4
    cvv
    opabbrex
    sylancr
    fvmptd
    ex
    @0
    wn
    #
    @8
    wph
    @19
    @1
    c0
    @7
    cZ
    cM
    fvprc
    @19
    @6
    wn
    #
    vy
    wal
    vx
    wal
    @7
    c0
    wceq
    @19
    @20
    vx
    vy
    @19
    @5
    wps
    @19
    @5
    @2
    @3
    c0
    wbr
    @2
    @3
    br0
    @19
    @4
    c0
    @2
    @3
    cZ
    cF
    fvprc
    breqd
    mtbiri
    intnanrd
    alrimivv
    @6
    vx
    vy
    opab0
    sylibr
    eqtr4d
    a1d
    pm2.61i
end
