include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "cmre.mm"
include "acsmre.mm"
include "mress.mm"
include "sylan.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "cdm.mm"
include "elfvdm.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "isacs2.mm"
include "simprbi.mm"
include "adantr.mm"
include "wceq.mm"
include "eleq1.mm"
include "pweq.mm"
include "ineq1d.mm"
include "sseq2.mm"
include "raleqbidv.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem acsfiel
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vz: setvar z
  let vx: setvar x
  assume isacs2.f: |- F = ( mrCls ` C )

  disjoint C y
  disjoint F y
  disjoint S y
  disjoint X y
  disjoint C c
  disjoint C f
  disjoint C s
  disjoint c f
  disjoint c s
  disjoint f s
  disjoint C t
  disjoint t y
  disjoint F f
  disjoint F s
  disjoint F t
  disjoint F z
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint t z
  disjoint y z
  disjoint S s
  disjoint X c
  disjoint X f
  disjoint X s
  disjoint X x
  disjoint c x
  disjoint f x
  disjoint s x
  disjoint X t
  assert |- ( C e. ( ACS ` X ) -> ( S e. C <-> ( S C_ X /\ A. y e. ( ~P S i^i Fin ) ( F ` y ) C_ S ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cS
    cC
    wcel
    #
    cS
    cX
    wss
    #
    @1
    wa
    @2
    vy
    cv
    cF
    cfv
    #
    cS
    wss
    #
    vy
    cS
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    @0
    @1
    @2
    @0
    @1
    @2
    @0
    cC
    cX
    cmre
    cfv
    wcel
    #
    @1
    @2
    cC
    cX
    acsmre
    cC
    cS
    cX
    mress
    sylan
    ex
    pm4.71rd
    @0
    @2
    @1
    @7
    @0
    @2
    wa
    cS
    cX
    cpw
    #
    wcel
    #
    vs
    cv
    #
    cC
    wcel
    #
    @3
    @11
    wss
    #
    vy
    @11
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wb
    #
    vs
    @9
    wral
    #
    @1
    @7
    wb
    #
    @0
    @10
    @2
    @0
    cX
    cacs
    cdm
    #
    wcel
    @10
    @2
    wb
    cC
    cX
    cacs
    elfvdm
    cS
    cX
    @20
    elpw2g
    syl
    biimpar
    @0
    @18
    @2
    @0
    @8
    @18
    vy
    cC
    cF
    cX
    vs
    isacs2.f
    isacs2
    simprbi
    adantr
    @17
    @19
    vs
    cS
    @9
    @11
    cS
    wceq
    #
    @12
    @1
    @16
    @7
    @11
    cS
    cC
    eleq1
    @21
    @13
    @4
    vy
    @15
    @6
    @21
    @14
    @5
    cfn
    @11
    cS
    pweq
    ineq1d
    @11
    cS
    @3
    sseq2
    raleqbidv
    bibi12d
    rspcva
    syl2anc
    pm5.32da
    bitrd
end
