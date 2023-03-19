include "wcel.mm"
include "cvv.mm"
include "wwe.mm"
include "wor.mm"
include "cmap.mm"
include "co.mm"
include "elex.mm"
include "w3a.mm"
include "ssid.mm"
include "simp1.mm"
include "weso.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "cdif.mm"
include "cdm.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "simpl1.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "simprll.mm"
include "elmapi.mm"
include "syl.mm"
include "ffn.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "simpl2.mm"
include "wefr.mm"
include "simprr.mm"
include "wb.mm"
include "simprlr.mm"
include "fndmdifeq0.mm"
include "syl2anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "fri.mm"
include "syl22anc.mm"
include "wemapsolem.mm"
include "syl3an1.mm"

theorem wemapso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cU: class U
  let cX: class X
  let cP: class P
  let cQ: class Q
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }

  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ( A e. V /\ R We A /\ S Or B ) -> T Or ( B ^m A ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cA
    cR
    wwe
    #
    cB
    cS
    wor
    #
    cB
    cA
    cmap
    co
    #
    cT
    wor
    cA
    cV
    elex
    @0
    @1
    @2
    w3a
    #
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    cS
    cT
    @3
    va
    vb
    vc
    vd
    wemapso.t
    @3
    ssid
    @0
    @1
    @2
    simp1
    @1
    @0
    cA
    cR
    wor
    @2
    cA
    cR
    weso
    3ad2ant2
    @0
    @1
    @2
    simp3
    @4
    va
    cv
    #
    @3
    wcel
    #
    vb
    cv
    #
    @3
    wcel
    #
    wa
    #
    @5
    @7
    wne
    #
    wa
    #
    wa
    #
    @5
    @7
    cdif
    #
    cdm
    #
    cvv
    wcel
    cA
    cR
    wfr
    #
    @14
    cA
    wss
    @14
    c0
    wne
    #
    vd
    cv
    vc
    cv
    cR
    wbr
    wn
    vd
    @14
    wral
    vc
    @14
    wrex
    @12
    @14
    cA
    cvv
    @0
    @1
    @2
    @11
    simpl1
    @12
    @5
    cdm
    #
    @14
    cA
    @13
    @5
    wss
    @14
    @17
    wss
    @5
    @7
    difss
    @13
    @5
    dmss
    ax-mp
    @12
    @5
    cA
    wfn
    #
    @17
    cA
    wceq
    @12
    cA
    cB
    @5
    wf
    #
    @18
    @12
    @6
    @19
    @4
    @6
    @8
    @10
    simprll
    @5
    cB
    cA
    elmapi
    syl
    cA
    cB
    @5
    ffn
    syl
    #
    cA
    @5
    fndm
    syl
    syl5sseq
    #
    ssexd
    @12
    @1
    @15
    @0
    @1
    @2
    @11
    simpl2
    cA
    cR
    wefr
    syl
    @21
    @12
    @16
    @10
    @4
    @9
    @10
    simprr
    @12
    @14
    c0
    @5
    @7
    @12
    @18
    @7
    cA
    wfn
    #
    @14
    c0
    wceq
    @5
    @7
    wceq
    wb
    @20
    @12
    cA
    cB
    @7
    wf
    #
    @22
    @12
    @8
    @23
    @4
    @6
    @8
    @10
    simprlr
    @7
    cB
    cA
    elmapi
    syl
    cA
    cB
    @7
    ffn
    syl
    cA
    @5
    @7
    fndmdifeq0
    syl2anc
    necon3bid
    mpbird
    vc
    vd
    cA
    @14
    cvv
    cR
    fri
    syl22anc
    wemapsolem
    syl3an1
end
