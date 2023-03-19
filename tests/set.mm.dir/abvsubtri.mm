include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "wbr.mm"
include "cgrp.mm"
include "crg.mm"
include "abvrcl.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "simp3.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "abvtri.mm"
include "syld3an3.mm"
include "abvneg.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"

theorem abvsubtri
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abvneg.b: |- B = ( Base ` R )
  assume abvsubtri.p: |- .- = ( -g ` R )


  assert |- ( ( F e. A /\ X e. B /\ Y e. B ) -> ( F ` ( X .- Y ) ) <_ ( ( F ` X ) + ( F ` Y ) ) )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.mi
    co
    #
    cF
    cfv
    cX
    cY
    cR
    cminusg
    cfv
    #
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    caddc
    co
    #
    cle
    @3
    @4
    @8
    cF
    @1
    @2
    @4
    @8
    wceq
    @0
    cB
    @7
    cR
    @5
    c.mi
    cX
    cY
    abvneg.b
    @7
    eqid
    #
    @5
    eqid
    #
    abvsubtri.p
    grpsubval
    3adant1
    fveq2d
    @3
    @9
    @10
    @6
    cF
    cfv
    #
    caddc
    co
    #
    @12
    cle
    @0
    @1
    @2
    @6
    cB
    wcel
    #
    @9
    @16
    cle
    wbr
    @3
    cR
    cgrp
    wcel
    #
    @2
    @17
    @3
    cR
    crg
    wcel
    #
    @18
    @0
    @1
    @19
    @2
    cA
    cR
    cF
    abv0.a
    abvrcl
    3ad2ant1
    cR
    ringgrp
    syl
    @0
    @1
    @2
    simp3
    cB
    cR
    @5
    cY
    abvneg.b
    @14
    grpinvcl
    syl2anc
    cA
    cB
    @7
    cR
    cF
    cX
    @6
    abv0.a
    abvneg.b
    @13
    abvtri
    syld3an3
    @3
    @15
    @11
    @10
    caddc
    @0
    @2
    @15
    @11
    wceq
    @1
    cA
    cB
    cR
    cF
    @5
    cY
    abv0.a
    abvneg.b
    @14
    abvneg
    3adant2
    oveq2d
    breqtrd
    eqbrtrd
end
