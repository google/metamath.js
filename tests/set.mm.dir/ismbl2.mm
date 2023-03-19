include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "ismbl.mm"
include "wb.mm"
include "elpwi.mm"
include "simprr.mm"
include "inss1.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "adantl.mm"
include "difss.mm"
include "readdcld.mm"
include "letri3d.mm"
include "cun.mm"
include "inundif.mm"
include "fveq2i.mm"
include "simprl.mm"
include "syl5ss.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "syl5eqbrr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "expr.mm"
include "pm5.74d.mm"
include "sylan2.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ismbl2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A e. dom vol <-> ( A C_ RR /\ A. x e. ~P RR ( ( vol* ` x ) e. RR -> ( ( vol* ` ( x i^i A ) ) + ( vol* ` ( x \ A ) ) ) <_ ( vol* ` x ) ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    cA
    cr
    wss
    #
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @2
    @1
    cA
    cin
    #
    covol
    cfv
    #
    @1
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    #
    wa
    @0
    @3
    @8
    @2
    cle
    wbr
    #
    wi
    #
    vx
    @11
    wral
    #
    wa
    vx
    cA
    ismbl
    @0
    @12
    @15
    @0
    @10
    @14
    vx
    @11
    @1
    @11
    wcel
    @0
    @1
    cr
    wss
    #
    @10
    @14
    wb
    @1
    cr
    elpwi
    @0
    @16
    wa
    @3
    @9
    @13
    @0
    @16
    @3
    @9
    @13
    wb
    @0
    @16
    @3
    wa
    #
    wa
    #
    @9
    @2
    @8
    cle
    wbr
    #
    @13
    wa
    @13
    @18
    @2
    @8
    @0
    @16
    @3
    simprr
    @18
    @5
    @7
    @17
    @5
    cr
    wcel
    #
    @0
    @4
    @1
    wss
    @16
    @3
    @20
    @1
    cA
    inss1
    #
    @4
    @1
    ovolsscl
    mp3an1
    adantl
    #
    @17
    @7
    cr
    wcel
    #
    @0
    @6
    @1
    wss
    @16
    @3
    @23
    @1
    cA
    difss
    #
    @6
    @1
    ovolsscl
    mp3an1
    adantl
    #
    readdcld
    letri3d
    @18
    @19
    @13
    @18
    @2
    @4
    @6
    cun
    #
    covol
    cfv
    #
    @8
    cle
    @26
    @1
    covol
    @1
    cA
    inundif
    fveq2i
    @18
    @4
    cr
    wss
    @20
    @6
    cr
    wss
    @23
    @27
    @8
    cle
    wbr
    @18
    @4
    @1
    cr
    @21
    @0
    @16
    @3
    simprl
    #
    syl5ss
    @22
    @18
    @6
    @1
    cr
    @24
    @28
    syl5ss
    @25
    @4
    @6
    ovolun
    syl22anc
    syl5eqbrr
    biantrurd
    bitr4d
    expr
    pm5.74d
    sylan2
    ralbidva
    pm5.32i
    bitri
end
