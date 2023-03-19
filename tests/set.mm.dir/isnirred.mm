include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "wral.mm"
include "cdif.mm"
include "eleq2i.mm"
include "eldif.mm"
include "bitri.mm"
include "baibr.mm"
include "wb.mm"
include "df-ne.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr2i.mm"
include "a1i.mm"
include "anbi12d.mm"
include "ioran.mm"
include "isirred.mm"
include "3bitr4g.mm"
include "con1bid.mm"

theorem isnirred
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cN: class N
  let cX: class X
  let vb: setvar b
  let vr: setvar r
  let vz: setvar z
  assume irred.1: |- B = ( Base ` R )
  assume irred.2: |- U = ( Unit ` R )
  assume irred.3: |- I = ( Irred ` R )
  assume irred.4: |- N = ( B \ U )
  assume irred.5: |- .x. = ( .r ` R )

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint N r
  disjoint x z
  disjoint y z
  disjoint N z
  disjoint R b
  disjoint R r
  disjoint R z
  disjoint .x. b
  disjoint .x. r
  disjoint .x. z
  disjoint X z
  assert |- ( X e. B -> ( -. X e. I <-> ( X e. U \/ E. x e. N E. y e. N ( x .x. y ) = X ) ) )

  proof
    cX
    cB
    wcel
    #
    cX
    cU
    wcel
    #
    vx
    cv
    vy
    cv
    c.x
    co
    #
    cX
    wceq
    #
    vy
    cN
    wrex
    #
    vx
    cN
    wrex
    #
    wo
    #
    cX
    cI
    wcel
    #
    @0
    @1
    wn
    #
    @5
    wn
    #
    wa
    cX
    cN
    wcel
    #
    @2
    cX
    wne
    #
    vy
    cN
    wral
    #
    vx
    cN
    wral
    #
    wa
    @6
    wn
    @7
    @0
    @8
    @10
    @9
    @13
    @10
    @0
    @8
    @10
    cX
    cB
    cU
    cdif
    #
    wcel
    @0
    @8
    wa
    cN
    @14
    cX
    irred.4
    eleq2i
    cX
    cB
    cU
    eldif
    bitri
    baibr
    @9
    @13
    wb
    @0
    @13
    @4
    wn
    #
    vx
    cN
    wral
    @9
    @12
    @15
    vx
    cN
    @12
    @3
    wn
    #
    vy
    cN
    wral
    @15
    @11
    @16
    vy
    cN
    @2
    cX
    df-ne
    ralbii
    @3
    vy
    cN
    ralnex
    bitri
    ralbii
    @4
    vx
    cN
    ralnex
    bitr2i
    a1i
    anbi12d
    @1
    @5
    ioran
    vx
    vy
    cB
    cR
    c.x
    cU
    cI
    cN
    cX
    irred.1
    irred.2
    irred.3
    irred.4
    irred.5
    isirred
    3bitr4g
    con1bid
end
