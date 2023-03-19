include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clindeps.mm"
include "wbr.mm"
include "clininds.mm"
include "wn.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "wne.mm"
include "wrex.mm"
include "w3a.mm"
include "wb.mm"
include "lindepsnlininds.mm"
include "ancoms.mm"
include "islininds.mm"
include "ibar.mm"
include "bicomd.mm"
include "adantl.mm"
include "bitrd.mm"
include "notbid.mm"
include "rexnal.mm"
include "df-ne.mm"
include "rexbii.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "pm4.61.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitr3i.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem islindeps
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  assume islindeps.b: |- B = ( Base ` M )
  assume islindeps.z: |- Z = ( 0g ` M )
  assume islindeps.r: |- R = ( Scalar ` M )
  assume islindeps.e: |- E = ( Base ` R )
  assume islindeps.0: |- .0. = ( 0g ` R )

  disjoint E f
  disjoint M f
  disjoint M x
  disjoint f x
  disjoint S f
  disjoint S x
  disjoint k x
  assert |- ( ( M e. W /\ S e. ~P B ) -> ( S linDepS M <-> E. f e. ( E ^m S ) ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z /\ E. x e. S ( f ` x ) =/= .0. ) ) )

  proof
    cM
    cW
    wcel
    #
    cS
    cB
    cpw
    #
    wcel
    #
    wa
    #
    cS
    cM
    clindeps
    wbr
    #
    cS
    cM
    clininds
    wbr
    #
    wn
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @7
    cS
    cM
    clinc
    cfv
    co
    cZ
    wceq
    #
    wa
    #
    vx
    cv
    @7
    cfv
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    wi
    #
    vf
    cE
    cS
    cmap
    co
    #
    wral
    #
    wn
    #
    @8
    @9
    @11
    c.0
    wne
    #
    vx
    cS
    wrex
    #
    w3a
    #
    vf
    @15
    wrex
    #
    @2
    @0
    @4
    @6
    wb
    cS
    cM
    @1
    cW
    lindepsnlininds
    ancoms
    @3
    @5
    @16
    @3
    @5
    @2
    @16
    wa
    #
    @16
    @2
    @0
    @5
    @22
    wb
    vx
    cB
    cR
    cS
    vf
    cE
    cM
    @1
    cW
    c.0
    cZ
    islindeps.b
    islindeps.z
    islindeps.r
    islindeps.e
    islindeps.0
    islininds
    ancoms
    @2
    @22
    @16
    wb
    @0
    @2
    @16
    @22
    @2
    @16
    ibar
    bicomd
    adantl
    bitrd
    notbid
    @17
    @21
    wb
    @3
    @17
    @14
    wn
    #
    vf
    @15
    wrex
    @21
    @14
    vf
    @15
    rexnal
    @23
    @20
    vf
    @15
    @10
    @13
    wn
    #
    wa
    @10
    @19
    wa
    @23
    @20
    @24
    @19
    @10
    @19
    @12
    wn
    #
    vx
    cS
    wrex
    @24
    @18
    @25
    vx
    cS
    @11
    c.0
    df-ne
    rexbii
    @12
    vx
    cS
    rexnal
    bitr2i
    anbi2i
    @10
    @13
    pm4.61
    @8
    @9
    @19
    df-3an
    3bitr4i
    rexbii
    bitr3i
    a1i
    3bitrd
end
