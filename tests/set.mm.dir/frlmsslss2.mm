include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cdif.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "crab.mm"
include "csupp.mm"
include "co.mm"
include "wa.mm"
include "cun.mm"
include "wfn.mm"
include "cvv.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "eqid.mm"
include "frlmbasf.mm"
include "3ad2antl2.mm"
include "ffn.mm"
include "syl.mm"
include "simpl3.mm"
include "undif.mm"
include "sylib.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "simpr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "disjdif.mm"
include "fnsuppres.mm"
include "syl121anc.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "difssd.mm"
include "frlmsslss.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem frlmsslss2
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  assume frlmsslss.y: |- Y = ( R freeLMod I )
  assume frlmsslss.u: |- U = ( LSubSp ` Y )
  assume frlmsslss.b: |- B = ( Base ` Y )
  assume frlmsslss.z: |- .0. = ( 0g ` R )
  assume frlmsslss2.c: |- C = { x e. B | ( x supp .0. ) C_ J }

  disjoint B x
  disjoint I x
  disjoint J x
  disjoint R x
  disjoint U x
  disjoint .0. x
  disjoint V x
  disjoint Y x
  assert |- ( ( R e. Ring /\ I e. V /\ J C_ I ) -> C e. U )

  proof
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    cJ
    cI
    wss
    #
    w3a
    #
    cC
    vx
    cv
    #
    cI
    cJ
    cdif
    #
    cres
    @5
    c.0
    csn
    cxp
    wceq
    #
    vx
    cB
    crab
    #
    cU
    @3
    cC
    @4
    c.0
    csupp
    co
    cJ
    wss
    #
    vx
    cB
    crab
    @7
    frlmsslss2.c
    @3
    @8
    @6
    vx
    cB
    @3
    @4
    cB
    wcel
    #
    wa
    #
    @4
    cJ
    @5
    cun
    #
    wfn
    #
    @9
    c.0
    cvv
    wcel
    #
    cJ
    @5
    cin
    c0
    wceq
    #
    @8
    @6
    wb
    @10
    @12
    @4
    cI
    wfn
    #
    @10
    cI
    cR
    cbs
    cfv
    #
    @4
    wf
    #
    @15
    @1
    @0
    @9
    @17
    @2
    cB
    cR
    cY
    cI
    @16
    cV
    @4
    frlmsslss.y
    @16
    eqid
    frlmsslss.b
    frlmbasf
    3ad2antl2
    cI
    @16
    @4
    ffn
    syl
    @10
    @11
    cI
    @4
    @10
    @2
    @11
    cI
    wceq
    @0
    @1
    @2
    @9
    simpl3
    cJ
    cI
    undif
    sylib
    fneq2d
    mpbird
    @3
    @9
    simpr
    @13
    @10
    c.0
    cR
    c0g
    cfv
    cvv
    frlmsslss.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    @14
    @10
    cJ
    cI
    disjdif
    a1i
    cJ
    @5
    @4
    cvv
    cB
    c.0
    fnsuppres
    syl121anc
    rabbidva
    syl5eq
    @0
    @1
    @2
    @5
    cI
    wss
    @7
    cU
    wcel
    @3
    cI
    cJ
    difssd
    vx
    cB
    @7
    cR
    cU
    cI
    @5
    cV
    cY
    c.0
    frlmsslss.y
    frlmsslss.u
    frlmsslss.b
    frlmsslss.z
    @7
    eqid
    frlmsslss
    syld3an3
    eqeltrd
end
