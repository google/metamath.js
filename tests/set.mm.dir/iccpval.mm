include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "cxr.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "ciccp.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-iccp.mm"
include "a1i.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "id.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem iccpval
  let vi: setvar i
  let cM: class M
  let vp: setvar p
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x

  disjoint i p
  disjoint M i
  disjoint M p
  disjoint i m
  disjoint m p
  disjoint M m
  disjoint k x
  assert |- ( M e. NN -> ( RePart ` M ) = { p e. ( RR* ^m ( 0 ... M ) ) | A. i e. ( 0 ..^ M ) ( p ` i ) < ( p ` ( i + 1 ) ) } )

  proof
    cM
    cn
    wcel
    #
    vm
    cM
    vi
    cv
    #
    vp
    cv
    #
    cfv
    @1
    c1
    caddc
    co
    @2
    cfv
    clt
    wbr
    #
    vi
    cc0
    vm
    cv
    #
    cfzo
    co
    #
    wral
    #
    vp
    cxr
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    @3
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    vp
    cxr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cn
    ciccp
    cvv
    ciccp
    vm
    cn
    @9
    cmpt
    wceq
    @0
    vi
    vm
    vp
    df-iccp
    a1i
    @4
    cM
    wceq
    #
    @9
    @14
    wceq
    @0
    @15
    @6
    @11
    vp
    @8
    @13
    @15
    @7
    @12
    cxr
    cmap
    @4
    cM
    cc0
    cfz
    oveq2
    oveq2d
    @15
    @3
    vi
    @5
    @10
    @4
    cM
    cc0
    cfzo
    oveq2
    raleqdv
    rabeqbidv
    adantl
    @0
    id
    @14
    cvv
    wcel
    @0
    @11
    vp
    @13
    cxr
    @12
    cmap
    ovex
    rabex
    a1i
    fvmptd
end
