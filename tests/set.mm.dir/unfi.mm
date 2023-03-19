include "cfn.mm"
include "wcel.mm"
include "cdif.mm"
include "cun.mm"
include "diffi.mm"
include "wa.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "reeanv.mm"
include "isfi.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "coa.mm"
include "co.mm"
include "nnacl.mm"
include "wi.mm"
include "unfilem3.mm"
include "entr.mm"
include "expcom.mm"
include "syl.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "unen.mm"
include "mpanr12.mm"
include "undif2.mm"
include "a1i.mm"
include "wss.mm"
include "nnaword1.mm"
include "undif.mm"
include "sylib.mm"
include "breq12d.mm"
include "syl5ib.mm"
include "sylan2d.mm"
include "breq2.mm"
include "rspcev.mm"
include "sylibr.mm"
include "syl6an.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "sylan2.mm"

theorem unfi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( A u. B ) e. Fin )

  proof
    cB
    cfn
    wcel
    cA
    cfn
    wcel
    #
    cB
    cA
    cdif
    #
    cfn
    wcel
    #
    cA
    cB
    cun
    #
    cfn
    wcel
    #
    cB
    cA
    diffi
    @0
    @2
    wa
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @1
    vy
    cv
    #
    cen
    wbr
    #
    wa
    #
    vy
    com
    wrex
    vx
    com
    wrex
    #
    @4
    @11
    @7
    vx
    com
    wrex
    #
    @9
    vy
    com
    wrex
    #
    wa
    @5
    @7
    @9
    vx
    vy
    com
    com
    reeanv
    @0
    @12
    @2
    @13
    vx
    cA
    isfi
    vy
    @1
    isfi
    anbi12i
    bitr4i
    @10
    @4
    vx
    vy
    com
    com
    @6
    com
    wcel
    @8
    com
    wcel
    wa
    #
    @6
    @8
    coa
    co
    #
    com
    wcel
    #
    @10
    @3
    @15
    cen
    wbr
    #
    @4
    @6
    @8
    nnacl
    @14
    @9
    @1
    @15
    @6
    cdif
    #
    cen
    wbr
    #
    @7
    @17
    @14
    @8
    @18
    cen
    wbr
    #
    @9
    @19
    wi
    @6
    @8
    unfilem3
    @9
    @20
    @19
    @1
    @8
    @18
    entr
    expcom
    syl
    @7
    @19
    wa
    #
    cA
    @1
    cun
    #
    @6
    @18
    cun
    #
    cen
    wbr
    #
    @14
    @17
    @21
    cA
    @1
    cin
    c0
    wceq
    @6
    @18
    cin
    c0
    wceq
    @24
    cA
    cB
    disjdif
    @6
    @15
    disjdif
    cA
    @6
    @1
    @18
    unen
    mpanr12
    @14
    @22
    @3
    @23
    @15
    cen
    @22
    @3
    wceq
    @14
    cA
    cB
    undif2
    a1i
    @14
    @6
    @15
    wss
    @23
    @15
    wceq
    @6
    @8
    nnaword1
    @6
    @15
    undif
    sylib
    breq12d
    syl5ib
    sylan2d
    @16
    @17
    wa
    @3
    vz
    cv
    #
    cen
    wbr
    #
    vz
    com
    wrex
    @4
    @26
    @17
    vz
    @15
    com
    @25
    @15
    @3
    cen
    breq2
    rspcev
    vz
    @3
    isfi
    sylibr
    syl6an
    rexlimivv
    sylbir
    sylan2
end
