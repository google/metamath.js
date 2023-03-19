include "cnp.mm"
include "wcel.mm"
include "cnq.mm"
include "cv.mm"
include "wn.mm"
include "cplq.mm"
include "co.mm"
include "wa.mm"
include "wex.mm"
include "abeq2i.mm"
include "elprnq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "cltq.mm"
include "wbr.mm"
include "ltaddnq.mm"
include "ancoms.mm"
include "addcomnq.mm"
include "syl6breq.mm"
include "prcdnq.mm"
include "syl5.mm"
include "mpd.mm"
include "ex.mm"
include "adantld.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "prpssnq.mm"
include "sspsstrd.mm"

theorem ltexprlem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume ltexprlem.1: |- C = { x | E. y ( -. y e. A /\ ( y +Q x ) e. B ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint y z
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
  disjoint A z
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
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint C z
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
  assert |- ( B e. P. -> C C. Q. )

  proof
    cB
    cnp
    wcel
    #
    cC
    cB
    cnq
    @0
    vx
    cC
    cB
    vx
    cv
    #
    cC
    wcel
    vy
    cv
    #
    cA
    wcel
    wn
    #
    @2
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
    @0
    @1
    cB
    wcel
    #
    @7
    vx
    cC
    ltexprlem.1
    abeq2i
    @0
    @6
    @8
    vy
    @0
    @5
    @8
    @3
    @0
    @5
    @8
    @0
    @5
    wa
    #
    @2
    cnq
    wcel
    #
    @1
    cnq
    wcel
    #
    wa
    #
    @8
    @9
    @4
    cnq
    wcel
    @12
    cB
    @4
    elprnq
    @2
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
    syl
    @12
    @1
    @4
    cltq
    wbr
    @9
    @8
    @12
    @1
    @1
    @2
    cplq
    co
    #
    @4
    cltq
    @11
    @10
    @1
    @13
    cltq
    wbr
    @1
    @2
    ltaddnq
    ancoms
    @1
    @2
    addcomnq
    syl6breq
    cB
    @4
    @1
    prcdnq
    syl5
    mpd
    ex
    adantld
    exlimdv
    syl5bi
    ssrdv
    cB
    prpssnq
    sspsstrd
end
