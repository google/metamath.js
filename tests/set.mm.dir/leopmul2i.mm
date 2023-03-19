include "cr.mm"
include "wcel.mm"
include "cho.mm"
include "w3a.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cleo.mm"
include "chot.mm"
include "co.mm"
include "wa.mm"
include "ch0o.mm"
include "chod.mm"
include "wi.mm"
include "simp1.mm"
include "hmopd.mm"
include "ancoms.mm"
include "3adant1.mm"
include "leopmuli.mm"
include "exp32.mm"
include "syl2anc.mm"
include "imp.mm"
include "wb.mm"
include "leop3.mm"
include "adantr.mm"
include "hmopm.mm"
include "syl2an.mm"
include "3impdi.mm"
include "wceq.mm"
include "cc.mm"
include "chil.mm"
include "wf.mm"
include "recn.mm"
include "hmopf.mm"
include "hosubdi.mm"
include "syl3an.mm"
include "3com23.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "3imtr4d.mm"
include "impr.mm"

theorem leopmul2i
  let cA: class A
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u


  assert |- ( ( ( A e. RR /\ T e. HrmOp /\ U e. HrmOp ) /\ ( 0 <_ A /\ T <_op U ) ) -> ( A .op T ) <_op ( A .op U ) )

  proof
    cA
    cr
    wcel
    #
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    w3a
    #
    cc0
    cA
    cle
    wbr
    #
    cT
    cU
    cleo
    wbr
    #
    cA
    cT
    chot
    co
    #
    cA
    cU
    chot
    co
    #
    cleo
    wbr
    #
    @3
    @4
    wa
    ch0o
    cU
    cT
    chod
    co
    #
    cleo
    wbr
    #
    ch0o
    cA
    @9
    chot
    co
    #
    cleo
    wbr
    #
    @5
    @8
    @3
    @4
    @10
    @12
    wi
    #
    @3
    @0
    @9
    cho
    wcel
    #
    @4
    @13
    wi
    @0
    @1
    @2
    simp1
    @1
    @2
    @14
    @0
    @2
    @1
    @14
    cU
    cT
    hmopd
    ancoms
    3adant1
    @0
    @14
    wa
    @4
    @10
    @12
    cA
    @9
    leopmuli
    exp32
    syl2anc
    imp
    @3
    @5
    @10
    wb
    #
    @4
    @1
    @2
    @15
    @0
    cT
    cU
    leop3
    3adant1
    adantr
    @3
    @8
    @12
    wb
    @4
    @3
    @8
    ch0o
    @7
    @6
    chod
    co
    #
    cleo
    wbr
    #
    @12
    @0
    @1
    @2
    @8
    @17
    wb
    #
    @0
    @1
    wa
    @6
    cho
    wcel
    @7
    cho
    wcel
    @18
    @0
    @2
    wa
    cA
    cT
    hmopm
    cA
    cU
    hmopm
    @6
    @7
    leop3
    syl2an
    3impdi
    @3
    @11
    @16
    ch0o
    cleo
    @0
    @2
    @1
    @11
    @16
    wceq
    #
    @0
    cA
    cc
    wcel
    @2
    chil
    chil
    cU
    wf
    @1
    chil
    chil
    cT
    wf
    @19
    cA
    recn
    cU
    hmopf
    cT
    hmopf
    cA
    cU
    cT
    hosubdi
    syl3an
    3com23
    breq2d
    bitr4d
    adantr
    3imtr4d
    impr
end
