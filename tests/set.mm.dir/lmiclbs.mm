include "clmic.mm"
include "wbr.mm"
include "cv.mm"
include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "brlmic.mm"
include "n0.mm"
include "bitri.mm"
include "wa.mm"
include "cima.mm"
include "lmimlbs.mm"
include "ne0i.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem lmiclbs
  let cS: class S
  let cT: class T
  let cJ: class J
  let cK: class K
  let vb: setvar b
  let vf: setvar f
  assume lmimlbs.j: |- J = ( LBasis ` S )
  assume lmimlbs.k: |- K = ( LBasis ` T )


  assert |- ( S ~=m T -> ( J =/= (/) -> K =/= (/) ) )

  proof
    cS
    cT
    clmic
    wbr
    #
    vf
    cv
    #
    cS
    cT
    clmim
    co
    #
    wcel
    #
    vf
    wex
    #
    cJ
    c0
    wne
    #
    cK
    c0
    wne
    #
    wi
    #
    @0
    @2
    c0
    wne
    @4
    cS
    cT
    brlmic
    vf
    @2
    n0
    bitri
    @3
    @7
    vf
    @5
    vb
    cv
    #
    cJ
    wcel
    #
    vb
    wex
    @3
    @6
    vb
    cJ
    n0
    @3
    @9
    @6
    vb
    @3
    @9
    @6
    @3
    @9
    wa
    @1
    @8
    cima
    #
    cK
    wcel
    @6
    @8
    cS
    cT
    @1
    cJ
    cK
    lmimlbs.j
    lmimlbs.k
    lmimlbs
    cK
    @10
    ne0i
    syl
    ex
    exlimdv
    syl5bi
    exlimiv
    sylbi
end
