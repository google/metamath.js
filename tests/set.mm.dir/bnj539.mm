include "wsbc.mm"
include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "sbcbii.mm"
include "bnj538.mm"
include "cvv.mm"
include "wb.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "sbcel2gv.mm"
include "bnj525.mm"
include "imbi12i.mm"
include "bitri.mm"
include "ralbii.mm"

theorem bnj539
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let bnjwpsm: wff ps'
  assume bnj539.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )
  assume bnj539.2: |- ( ps' <-> [. M / n ]. ps )
  assume bnj539.3: |- M e. _V

  disjoint A n
  disjoint F n
  disjoint M i
  disjoint R n
  disjoint i n
  disjoint n y
  assert |- ( ps' <-> A. i e. _om ( suc i e. M -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwpsm
    wps
    vn
    cM
    wsbc
    #
    vi
    cv
    #
    csuc
    #
    cM
    wcel
    #
    @2
    cF
    cfv
    vy
    @1
    cF
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    bnj539.2
    @0
    @2
    vn
    cv
    wcel
    #
    @4
    wi
    #
    vi
    com
    wral
    #
    vn
    cM
    wsbc
    #
    @6
    wps
    @9
    vn
    cM
    bnj539.1
    sbcbii
    @10
    @8
    vn
    cM
    wsbc
    #
    vi
    com
    wral
    @6
    @8
    vi
    vn
    cM
    com
    bnj539.3
    bnj538
    @11
    @5
    vi
    com
    @11
    @7
    vn
    cM
    wsbc
    #
    @4
    vn
    cM
    wsbc
    #
    wi
    #
    @5
    cM
    cvv
    wcel
    #
    @11
    @14
    wb
    bnj539.3
    @7
    @4
    vn
    cM
    cvv
    sbcimg
    ax-mp
    @12
    @3
    @13
    @4
    @15
    @12
    @3
    wb
    bnj539.3
    vn
    @2
    cM
    cvv
    sbcel2gv
    ax-mp
    @4
    vn
    cM
    bnj539.3
    bnj525
    imbi12i
    bitri
    ralbii
    bitri
    bitri
    bitri
end
