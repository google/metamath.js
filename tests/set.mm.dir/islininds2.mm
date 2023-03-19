include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "cnzr.mm"
include "w3a.mm"
include "clininds.mm"
include "wbr.mm"
include "clindeps.mm"
include "wn.mm"
include "cv.mm"
include "cfsupp.mm"
include "csn.mm"
include "cdif.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wne.mm"
include "wo.mm"
include "cmap.mm"
include "wral.mm"
include "wb.mm"
include "lindepsnlininds.mm"
include "ancoms.mm"
include "3adant3.mm"
include "con2bid.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "notnotb.mm"
include "nne.mm"
include "bicomi.mm"
include "anbi12i.mm"
include "pm4.56.mm"
include "bitri.mm"
include "rexbii.mm"
include "rexnal.mm"
include "islindeps2.mm"
include "syl5bir.mm"
include "con1d.mm"
include "sylbid.mm"

theorem islininds2
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vg: setvar g
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume islindeps2.b: |- B = ( Base ` M )
  assume islindeps2.z: |- Z = ( 0g ` M )
  assume islindeps2.r: |- R = ( Scalar ` M )
  assume islindeps2.e: |- E = ( Base ` R )
  assume islindeps2.0: |- .0. = ( 0g ` R )

  disjoint B f
  disjoint B s
  disjoint f s
  disjoint E f
  disjoint E s
  disjoint M f
  disjoint M s
  disjoint R f
  disjoint R s
  disjoint S f
  disjoint S s
  disjoint Z f
  disjoint Z s
  disjoint .0. f
  disjoint .0. s
  disjoint B g
  disjoint B z
  disjoint f g
  disjoint f z
  disjoint g s
  disjoint g z
  disjoint s z
  disjoint E g
  disjoint E z
  disjoint M g
  disjoint M z
  disjoint R g
  disjoint R z
  disjoint S g
  disjoint S z
  disjoint Z g
  disjoint .0. g
  disjoint k x
  assert |- ( ( M e. LMod /\ S e. ~P B /\ R e. NzRing ) -> ( S linIndS M -> A. s e. S A. f e. ( E ^m ( S \ { s } ) ) ( -. f finSupp .0. \/ ( f ( linC ` M ) ( S \ { s } ) ) =/= s ) ) )

  proof
    cM
    clmod
    wcel
    #
    cS
    cB
    cpw
    #
    wcel
    #
    cR
    cnzr
    wcel
    #
    w3a
    #
    cS
    cM
    clininds
    wbr
    #
    cS
    cM
    clindeps
    wbr
    #
    wn
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    wn
    #
    @7
    cS
    vs
    cv
    #
    csn
    cdif
    #
    cM
    clinc
    cfv
    co
    #
    @10
    wne
    #
    wo
    #
    vf
    cE
    @11
    cmap
    co
    #
    wral
    #
    vs
    cS
    wral
    #
    @4
    @6
    @5
    @0
    @2
    @6
    @5
    wn
    wb
    #
    @3
    @2
    @0
    @18
    cS
    cM
    @1
    clmod
    lindepsnlininds
    ancoms
    3adant3
    con2bid
    @4
    @17
    @6
    @17
    wn
    #
    @8
    @12
    @10
    wceq
    #
    wa
    #
    vf
    @15
    wrex
    #
    vs
    cS
    wrex
    #
    @4
    @6
    @23
    @16
    wn
    #
    vs
    cS
    wrex
    @19
    @22
    @24
    vs
    cS
    @22
    @14
    wn
    #
    vf
    @15
    wrex
    @24
    @21
    @25
    vf
    @15
    @21
    @9
    wn
    #
    @13
    wn
    #
    wa
    @25
    @8
    @26
    @20
    @27
    @8
    notnotb
    @27
    @20
    @12
    @10
    nne
    bicomi
    anbi12i
    @9
    @13
    pm4.56
    bitri
    rexbii
    @14
    vf
    @15
    rexnal
    bitri
    rexbii
    @16
    vs
    cS
    rexnal
    bitri
    cB
    cR
    cS
    vf
    cE
    cM
    c.0
    cZ
    vs
    islindeps2.b
    islindeps2.z
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps2
    syl5bir
    con1d
    sylbid
end
