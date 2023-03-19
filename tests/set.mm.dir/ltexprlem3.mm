include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "cplq.mm"
include "co.mm"
include "wex.mm"
include "cnq.mm"
include "wb.mm"
include "elprnq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "simpld.mm"
include "ltanq.mm"
include "3syl.mm"
include "prcdnq.mm"
include "sylbid.mm"
include "impancom.mm"
include "anim2d.mm"
include "eximdv.mm"
include "abeq2i.mm"
include "vex.mm"
include "weq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab2.mm"
include "3imtr4g.mm"
include "ex.mm"
include "com23.mm"
include "alrimdv.mm"

theorem ltexprlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume ltexprlem.1: |- C = { x | E. y ( -. y e. A /\ ( y +Q x ) e. B ) }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint w y
  disjoint v y
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint v w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint A w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint A v
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B w
  disjoint B v
  disjoint C w
  disjoint C v
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  disjoint f u
  disjoint g u
  disjoint h u
  assert |- ( B e. P. -> ( x e. C -> A. z ( z <Q x -> z e. C ) ) )

  proof
    cB
    cnp
    wcel
    #
    vx
    cv
    #
    cC
    wcel
    #
    vz
    cv
    #
    @1
    cltq
    wbr
    #
    @3
    cC
    wcel
    #
    wi
    vz
    @0
    @4
    @2
    @5
    @0
    @4
    @2
    @5
    wi
    @0
    @4
    wa
    #
    vy
    cv
    #
    cA
    wcel
    wn
    #
    @7
    @1
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    @8
    @7
    @3
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    @2
    @5
    @6
    @11
    @15
    vy
    @6
    @10
    @14
    @8
    @0
    @10
    @4
    @14
    @0
    @10
    wa
    #
    @4
    @13
    @9
    cltq
    wbr
    #
    @14
    @17
    @9
    cnq
    wcel
    #
    @7
    cnq
    wcel
    #
    @4
    @18
    wb
    cB
    @9
    elprnq
    @19
    @20
    @1
    cnq
    wcel
    @7
    @1
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    simpld
    @3
    @1
    @7
    ltanq
    3syl
    cB
    @9
    @13
    prcdnq
    sylbid
    impancom
    anim2d
    eximdv
    @12
    vx
    cC
    ltexprlem.1
    abeq2i
    @12
    @16
    vx
    @3
    cC
    vz
    vex
    vx
    vz
    weq
    #
    @11
    @15
    vy
    @21
    @10
    @14
    @8
    @21
    @9
    @13
    cB
    @1
    @3
    @7
    cplq
    oveq2
    eleq1d
    anbi2d
    exbidv
    ltexprlem.1
    elab2
    3imtr4g
    ex
    com23
    alrimdv
end
