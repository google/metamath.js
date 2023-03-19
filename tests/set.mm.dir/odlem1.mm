include "wcel.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wa.mm"
include "wo.mm"
include "odval.mm"
include "wi.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "orc.mm"
include "expcom.mm"
include "adantl.mm"
include "wn.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "cn.mm"
include "crab.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "eqcomi.mm"
include "3sstr4i.mm"
include "df-ne.mm"
include "biimpri.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eleq1a.mm"
include "syl.mm"
include "olc.mm"
include "syl6.mm"
include "ifbothda.mm"
include "mpd.mm"

theorem odlem1
  let vy: setvar y
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vi: setvar i
  let vx: setvar x
  assume odval.1: |- X = ( Base ` G )
  assume odval.2: |- .x. = ( .g ` G )
  assume odval.3: |- .0. = ( 0g ` G )
  assume odval.4: |- O = ( od ` G )
  assume odval.i: |- I = { y e. NN | ( y .x. A ) = .0. }

  disjoint A y
  disjoint G y
  disjoint .x. y
  disjoint .0. y
  disjoint g i
  disjoint g y
  disjoint i y
  disjoint x y
  disjoint A x
  disjoint g x
  disjoint G g
  disjoint G x
  disjoint .x. g
  disjoint .x. x
  disjoint .0. g
  disjoint .0. x
  disjoint i x
  disjoint I i
  disjoint I x
  disjoint X g
  disjoint X x
  assert |- ( A e. X -> ( ( ( O ` A ) = 0 /\ I = (/) ) \/ ( O ` A ) e. I ) )

  proof
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cI
    c0
    wceq
    #
    cc0
    cI
    cr
    clt
    cinf
    #
    cif
    #
    wceq
    #
    @1
    cc0
    wceq
    #
    @2
    wa
    #
    @1
    cI
    wcel
    #
    wo
    #
    vy
    cA
    c.x
    cG
    cI
    cO
    cX
    c.0
    odval.1
    odval.2
    odval.3
    odval.4
    odval.i
    odval
    @2
    @6
    @9
    wi
    #
    @1
    @3
    wceq
    #
    @9
    wi
    @5
    @9
    wi
    @0
    cc0
    @3
    cc0
    @4
    wceq
    @6
    @5
    @9
    cc0
    @4
    @1
    eqeq2
    imbi1d
    @3
    @4
    wceq
    @11
    @5
    @9
    @3
    @4
    @1
    eqeq2
    imbi1d
    @2
    @10
    @0
    @6
    @2
    @9
    @7
    @8
    orc
    expcom
    adantl
    @0
    @2
    wn
    #
    wa
    #
    @11
    @8
    @9
    @13
    @3
    cI
    wcel
    #
    @11
    @8
    wi
    @13
    cI
    c1
    cuz
    cfv
    #
    wss
    cI
    c0
    wne
    #
    @14
    vy
    cv
    cA
    c.x
    co
    c.0
    wceq
    #
    vy
    cn
    crab
    cn
    cI
    @15
    @17
    vy
    cn
    ssrab2
    odval.i
    cn
    @15
    nnuz
    eqcomi
    3sstr4i
    @12
    @16
    @0
    @16
    @12
    cI
    c0
    df-ne
    biimpri
    adantl
    cI
    c1
    infssuzcl
    sylancr
    @3
    cI
    @1
    eleq1a
    syl
    @8
    @7
    olc
    syl6
    ifbothda
    mpd
end
