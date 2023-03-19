include "cv.mm"
include "whe.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "wb.mm"
include "dffrege76.mm"
include "wsbc.mm"
include "frege68c.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "csb.mm"
include "sbcheg.mm"
include "wceq.mm"
include "csbconstg.mm"
include "csbvarg.mm"
include "heeq12.mm"
include "mp2an.mm"
include "bitri.mm"
include "sbcal.mm"
include "sbcg.mm"
include "sbcel2gv.mm"
include "imbi12i.mm"
include "albii.mm"
include "syl6ib.mm"

theorem frege77
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vf: setvar f
  assume frege77.x: |- X e. U
  assume frege77.y: |- Y e. V
  assume frege77.r: |- R e. W
  assume frege77.a: |- A e. B

  disjoint A a
  disjoint R a
  disjoint X a
  disjoint a f
  disjoint R f
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint Y f
  assert |- ( X ( t+ ` R ) Y -> ( R hereditary A -> ( A. a ( X R a -> a e. A ) -> Y e. A ) ) )

  proof
    vf
    cv
    #
    cR
    whe
    #
    cX
    va
    cv
    #
    cR
    wbr
    #
    va
    vf
    wel
    #
    wi
    #
    va
    wal
    #
    cY
    @0
    wcel
    #
    wi
    #
    wi
    #
    vf
    wal
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    #
    wb
    #
    @10
    cA
    cR
    whe
    #
    @3
    @2
    cA
    wcel
    #
    wi
    #
    va
    wal
    #
    cY
    cA
    wcel
    #
    wi
    #
    wi
    #
    wi
    cX
    cR
    cU
    vf
    cY
    cV
    cW
    va
    frege77.x
    frege77.y
    frege77.r
    dffrege76
    @11
    @10
    @9
    vf
    cA
    wsbc
    #
    @18
    @9
    @10
    vf
    cA
    cB
    frege77.a
    frege68c
    @19
    @1
    vf
    cA
    wsbc
    #
    @8
    vf
    cA
    wsbc
    #
    wi
    #
    @18
    cA
    cB
    wcel
    #
    @19
    @22
    wb
    frege77.a
    @1
    @8
    vf
    cA
    cB
    sbcimg
    ax-mp
    @20
    @12
    @21
    @17
    @20
    vf
    cA
    @0
    csb
    #
    vf
    cA
    cR
    csb
    #
    whe
    #
    @12
    @23
    @20
    @26
    wb
    frege77.a
    vf
    cA
    cR
    @0
    cB
    sbcheg
    ax-mp
    @25
    cR
    wceq
    #
    @24
    cA
    wceq
    #
    @26
    @12
    wb
    @23
    @27
    frege77.a
    vf
    cA
    cR
    cB
    csbconstg
    ax-mp
    @23
    @28
    frege77.a
    vf
    cA
    cB
    csbvarg
    ax-mp
    @24
    cA
    @25
    cR
    heeq12
    mp2an
    bitri
    @21
    @6
    vf
    cA
    wsbc
    #
    @7
    vf
    cA
    wsbc
    #
    wi
    #
    @17
    @23
    @21
    @31
    wb
    frege77.a
    @6
    @7
    vf
    cA
    cB
    sbcimg
    ax-mp
    @29
    @15
    @30
    @16
    @29
    @5
    vf
    cA
    wsbc
    #
    va
    wal
    @15
    @5
    va
    vf
    cA
    sbcal
    @32
    @14
    va
    @32
    @3
    vf
    cA
    wsbc
    #
    @4
    vf
    cA
    wsbc
    #
    wi
    #
    @14
    @23
    @32
    @35
    wb
    frege77.a
    @3
    @4
    vf
    cA
    cB
    sbcimg
    ax-mp
    @33
    @3
    @34
    @13
    @23
    @33
    @3
    wb
    frege77.a
    @3
    vf
    cA
    cB
    sbcg
    ax-mp
    @23
    @34
    @13
    wb
    frege77.a
    vf
    @2
    cA
    cB
    sbcel2gv
    ax-mp
    imbi12i
    bitri
    albii
    bitri
    @23
    @30
    @16
    wb
    frege77.a
    vf
    cY
    cA
    cB
    sbcel2gv
    ax-mp
    imbi12i
    bitri
    imbi12i
    bitri
    syl6ib
    ax-mp
end
