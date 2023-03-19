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
include "3bitri.mm"

theorem bnj92
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cZ: class Z
  assume bnj92.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj92.2: |- Z e. _V

  disjoint A n
  disjoint R n
  disjoint Z i
  disjoint f n
  disjoint i n
  disjoint n y
  assert |- ( [. Z / n ]. ps <-> A. i e. _om ( suc i e. Z -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  proof
    wps
    vn
    cZ
    wsbc
    vi
    cv
    #
    csuc
    #
    vn
    cv
    wcel
    #
    @1
    vf
    cv
    #
    cfv
    vy
    @0
    @3
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
    vn
    cZ
    wsbc
    @5
    vn
    cZ
    wsbc
    #
    vi
    com
    wral
    @1
    cZ
    wcel
    #
    @4
    wi
    #
    vi
    com
    wral
    wps
    @6
    vn
    cZ
    bnj92.1
    sbcbii
    @5
    vi
    vn
    cZ
    com
    bnj92.2
    bnj538
    @7
    @9
    vi
    com
    @7
    @2
    vn
    cZ
    wsbc
    #
    @4
    vn
    cZ
    wsbc
    #
    wi
    #
    @9
    cZ
    cvv
    wcel
    #
    @7
    @12
    wb
    bnj92.2
    @2
    @4
    vn
    cZ
    cvv
    sbcimg
    ax-mp
    @10
    @8
    @11
    @4
    @13
    @10
    @8
    wb
    bnj92.2
    vn
    @1
    cZ
    cvv
    sbcel2gv
    ax-mp
    @4
    vn
    cZ
    bnj92.2
    bnj525
    imbi12i
    bitri
    ralbii
    3bitri
end
