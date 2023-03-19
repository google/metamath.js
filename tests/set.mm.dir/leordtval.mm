include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "leordtval2.mm"
include "ctsr.mm"
include "wcel.mm"
include "wceq.mm"
include "letsr.mm"
include "cxr.mm"
include "ledm.mm"
include "leordtvallem1.mm"
include "leordtvallem2.mm"
include "cioo.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "crab.mm"
include "cmpt2.mm"
include "clt.mm"
include "df-ioo.mm"
include "wb.mm"
include "xrltnle.mm"
include "adantlr.mm"
include "ancoms.mm"
include "adantll.mm"
include "anbi12d.mm"
include "rabbidva.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "rneqi.mm"
include "ordtbas2.mm"
include "ax-mp.mm"
include "fveq2i.mm"

theorem leordtval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume leordtval.1: |- A = ran ( x e. RR* |-> ( x (,] +oo ) )
  assume leordtval.2: |- B = ran ( x e. RR* |-> ( -oo [,) x ) )
  assume leordtval.3: |- C = ran (,)


  assert |- ( ordTop ` <_ ) = ( topGen ` ( ( A u. B ) u. C ) )

  proof
    cle
    cordt
    cfv
    cA
    cB
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    @0
    cC
    cun
    #
    ctg
    cfv
    vx
    cA
    cB
    leordtval.1
    leordtval.2
    leordtval2
    @1
    @2
    ctg
    cle
    ctsr
    wcel
    @1
    @2
    wceq
    letsr
    vx
    vy
    cA
    cB
    cC
    cle
    cxr
    va
    vb
    ledm
    vx
    vy
    cA
    leordtval.1
    leordtvallem1
    vx
    vy
    cA
    cB
    leordtval.1
    leordtval.2
    leordtvallem2
    cC
    cioo
    crn
    va
    vb
    cxr
    cxr
    vy
    cv
    #
    va
    cv
    #
    cle
    wbr
    wn
    #
    vb
    cv
    #
    @3
    cle
    wbr
    wn
    #
    wa
    #
    vy
    cxr
    crab
    #
    cmpt2
    #
    crn
    leordtval.3
    cioo
    @10
    cioo
    va
    vb
    cxr
    cxr
    @4
    @3
    clt
    wbr
    #
    @3
    @6
    clt
    wbr
    #
    wa
    #
    vy
    cxr
    crab
    #
    cmpt2
    @10
    va
    vb
    vy
    df-ioo
    va
    vb
    cxr
    cxr
    @14
    @9
    @4
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    wa
    #
    @13
    @8
    vy
    cxr
    @17
    @3
    cxr
    wcel
    #
    wa
    @11
    @5
    @12
    @7
    @15
    @18
    @11
    @5
    wb
    @16
    @4
    @3
    xrltnle
    adantlr
    @16
    @18
    @12
    @7
    wb
    #
    @15
    @18
    @16
    @19
    @3
    @6
    xrltnle
    ancoms
    adantll
    anbi12d
    rabbidva
    mpt2eq3ia
    eqtri
    rneqi
    eqtri
    ordtbas2
    ax-mp
    fveq2i
    eqtri
end
