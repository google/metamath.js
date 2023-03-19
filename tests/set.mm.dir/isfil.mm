include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "cfil.mm"
include "cdm.mm"
include "df-fil.mm"
include "wceq.mm"
include "wa.mm"
include "pweq.mm"
include "adantr.mm"
include "wb.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "fveq2.mm"
include "fvex.mm"
include "elfvdm.mm"
include "elmptrab2.mm"

theorem isfil
  let vx: setvar x
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vz: setvar z

  disjoint F x
  disjoint X x
  disjoint F f
  disjoint F z
  disjoint f x
  disjoint f z
  disjoint x z
  disjoint X f
  disjoint X z
  assert |- ( F e. ( Fil ` X ) <-> ( F e. ( fBas ` X ) /\ A. x e. ~P X ( ( F i^i ~P x ) =/= (/) -> x e. F ) ) )

  proof
    vf
    cv
    #
    vx
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    vf
    wel
    #
    wi
    #
    vx
    vz
    cv
    #
    cpw
    #
    wral
    cF
    @2
    cin
    #
    c0
    wne
    #
    @1
    cF
    wcel
    #
    wi
    #
    vx
    cX
    cpw
    #
    wral
    vz
    vf
    @7
    cfbas
    cfv
    cX
    cfbas
    cfv
    cfil
    cfbas
    cdm
    cX
    cF
    vx
    vz
    vf
    df-fil
    @7
    cX
    wceq
    #
    @0
    cF
    wceq
    #
    wa
    @6
    @12
    vx
    @8
    @13
    @14
    @8
    @13
    wceq
    @15
    @7
    cX
    pweq
    adantr
    @15
    @6
    @12
    wb
    @14
    @15
    @4
    @10
    @5
    @11
    @15
    @3
    @9
    c0
    @0
    cF
    @2
    ineq1
    neeq1d
    @0
    cF
    @1
    eleq2
    imbi12d
    adantl
    raleqbidv
    @7
    cX
    cfbas
    fveq2
    @7
    cfbas
    fvex
    cF
    cX
    cfbas
    elfvdm
    elmptrab2
end
