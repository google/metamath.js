include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wa.mm"
include "wo.mm"
include "gexval.mm"
include "wi.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "orc.mm"
include "expcom.mm"
include "adantl.mm"
include "wn.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
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

theorem gexlem1
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vi: setvar i
  assume gexval.1: |- X = ( Base ` G )
  assume gexval.2: |- .x. = ( .g ` G )
  assume gexval.3: |- .0. = ( 0g ` G )
  assume gexval.4: |- E = ( gEx ` G )
  assume gexval.i: |- I = { y e. NN | A. x e. X ( y .x. x ) = .0. }

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint V y
  disjoint .x. x
  disjoint .x. y
  disjoint X x
  disjoint g i
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint i x
  disjoint i y
  disjoint G i
  disjoint I g
  disjoint I i
  disjoint V g
  disjoint V i
  assert |- ( G e. V -> ( ( E = 0 /\ I = (/) ) \/ E e. I ) )

  proof
    cG
    cV
    wcel
    #
    cE
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
    cE
    cc0
    wceq
    #
    @1
    wa
    #
    cE
    cI
    wcel
    #
    wo
    #
    vx
    vy
    c.x
    cE
    cG
    cI
    cV
    cX
    c.0
    gexval.1
    gexval.2
    gexval.3
    gexval.4
    gexval.i
    gexval
    @1
    @5
    @8
    wi
    #
    cE
    @2
    wceq
    #
    @8
    wi
    @4
    @8
    wi
    @0
    cc0
    @2
    cc0
    @3
    wceq
    @5
    @4
    @8
    cc0
    @3
    cE
    eqeq2
    imbi1d
    @2
    @3
    wceq
    @10
    @4
    @8
    @2
    @3
    cE
    eqeq2
    imbi1d
    @1
    @9
    @0
    @5
    @1
    @8
    @6
    @7
    orc
    expcom
    adantl
    @0
    @1
    wn
    #
    wa
    #
    @10
    @7
    @8
    @12
    @2
    cI
    wcel
    #
    @10
    @7
    wi
    @12
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
    @13
    vy
    cv
    vx
    cv
    c.x
    co
    c.0
    wceq
    vx
    cX
    wral
    #
    vy
    cn
    crab
    cn
    cI
    @14
    @16
    vy
    cn
    ssrab2
    gexval.i
    cn
    @14
    nnuz
    eqcomi
    3sstr4i
    @11
    @15
    @0
    @15
    @11
    cI
    c0
    df-ne
    biimpri
    adantl
    cI
    c1
    infssuzcl
    sylancr
    @2
    cI
    cE
    eleq1a
    syl
    @7
    @6
    olc
    syl6
    ifbothda
    mpd
end
