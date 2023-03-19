include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "w3a.mm"
include "om1elbas.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simp3d.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "pcocn.mm"
include "pco0.mm"
include "eqtrd.mm"
include "pco1.mm"
include "mpbir3and.mm"

theorem om1addcl
  let wph: wff ph
  let cB: class B
  let cH: class H
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let cF: class F
  let vf: setvar f
  assume om1bas.o: |- O = ( J Om1 Y )
  assume om1bas.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1bas.y: |- ( ph -> Y e. X )
  assume om1bas.b: |- ( ph -> B = ( Base ` O ) )
  assume om1addcl.h: |- ( ph -> H e. B )
  assume om1addcl.k: |- ( ph -> K e. B )


  assert |- ( ph -> ( H ( *p ` J ) K ) e. B )

  proof
    wph
    cH
    cK
    cJ
    cpco
    cfv
    co
    #
    cB
    wcel
    @0
    cii
    cJ
    ccn
    co
    #
    wcel
    cc0
    @0
    cfv
    #
    cY
    wceq
    c1
    @0
    cfv
    #
    cY
    wceq
    wph
    cH
    cK
    cJ
    wph
    cH
    @1
    wcel
    #
    cc0
    cH
    cfv
    #
    cY
    wceq
    #
    c1
    cH
    cfv
    #
    cY
    wceq
    #
    wph
    cH
    cB
    wcel
    @4
    @6
    @8
    w3a
    om1addcl.h
    wph
    cB
    cH
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    om1bas.b
    om1elbas
    mpbid
    #
    simp1d
    #
    wph
    cK
    @1
    wcel
    #
    cc0
    cK
    cfv
    #
    cY
    wceq
    #
    c1
    cK
    cfv
    #
    cY
    wceq
    #
    wph
    cK
    cB
    wcel
    @11
    @13
    @15
    w3a
    om1addcl.k
    wph
    cB
    cK
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    om1bas.b
    om1elbas
    mpbid
    #
    simp1d
    #
    wph
    @7
    cY
    @12
    wph
    @4
    @6
    @8
    @9
    simp3d
    wph
    @11
    @13
    @15
    @16
    simp2d
    eqtr4d
    pcocn
    wph
    @2
    @5
    cY
    wph
    cH
    cK
    cJ
    @10
    @17
    pco0
    wph
    @4
    @6
    @8
    @9
    simp2d
    eqtrd
    wph
    @3
    @14
    cY
    wph
    cH
    cK
    cJ
    @10
    @17
    pco1
    wph
    @11
    @13
    @15
    @16
    simp3d
    eqtrd
    wph
    cB
    @0
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    om1bas.b
    om1elbas
    mpbir3and
end
