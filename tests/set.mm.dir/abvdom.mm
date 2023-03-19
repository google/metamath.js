include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "cmul.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "abvmul.mm"
include "syl3anc.mm"
include "cr.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "simp2r.mm"
include "abvne0.mm"
include "simp3r.mm"
include "mulne0d.mm"
include "eqnetrd.mm"
include "abv0.mm"
include "syl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "mpd.mm"

theorem abvdom
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abvneg.b: |- B = ( Base ` R )
  assume abvrec.z: |- .0. = ( 0g ` R )
  assume abvdom.t: |- .x. = ( .r ` R )


  assert |- ( ( F e. A /\ ( X e. B /\ X =/= .0. ) /\ ( Y e. B /\ Y =/= .0. ) ) -> ( X .x. Y ) =/= .0. )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    wa
    #
    cY
    cB
    wcel
    #
    cY
    c.0
    wne
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    #
    cc0
    wne
    @8
    c.0
    wne
    @7
    @9
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cmul
    co
    #
    cc0
    @7
    @0
    @1
    @4
    @9
    @12
    wceq
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2l
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    cA
    cB
    cR
    c.x
    cF
    cX
    cY
    abv0.a
    abvneg.b
    abvdom.t
    abvmul
    syl3anc
    @7
    @10
    @11
    @7
    @10
    @7
    @0
    @1
    @10
    cr
    wcel
    @13
    @14
    cA
    cB
    cR
    cF
    cX
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @7
    @11
    @7
    @0
    @4
    @11
    cr
    wcel
    @13
    @15
    cA
    cB
    cR
    cF
    cY
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @7
    @0
    @1
    @2
    @10
    cc0
    wne
    @13
    @14
    @0
    @1
    @2
    @6
    simp2r
    cA
    cB
    cR
    cF
    cX
    c.0
    abv0.a
    abvneg.b
    abvrec.z
    abvne0
    syl3anc
    @7
    @0
    @4
    @5
    @11
    cc0
    wne
    @13
    @15
    @0
    @3
    @4
    @5
    simp3r
    cA
    cB
    cR
    cF
    cY
    c.0
    abv0.a
    abvneg.b
    abvrec.z
    abvne0
    syl3anc
    mulne0d
    eqnetrd
    @7
    @8
    c.0
    @9
    cc0
    @7
    @9
    cc0
    wceq
    @8
    c.0
    wceq
    #
    c.0
    cF
    cfv
    #
    cc0
    wceq
    #
    @7
    @0
    @18
    @13
    cA
    cR
    cF
    c.0
    abv0.a
    abvrec.z
    abv0
    syl
    @16
    @9
    @17
    cc0
    @8
    c.0
    cF
    fveq2
    eqeq1d
    syl5ibrcom
    necon3d
    mpd
end
