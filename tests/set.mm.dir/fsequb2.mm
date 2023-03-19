include "cfz.mm"
include "co.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "wrex.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfi.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "fimaxre3.mm"
include "sylancr.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "syl.mm"
include "rexbidv.mm"
include "mpbird.mm"

theorem fsequb2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint M k
  disjoint N k
  assert |- ( F : ( M ... N ) --> RR -> E. x e. RR A. y e. ran F y <_ x )

  proof
    cM
    cN
    cfz
    co
    #
    cr
    cF
    wf
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cF
    crn
    wral
    #
    vx
    cr
    wrex
    vk
    cv
    #
    cF
    cfv
    #
    @3
    cle
    wbr
    #
    vk
    @0
    wral
    #
    vx
    cr
    wrex
    #
    @1
    @0
    cfn
    wcel
    @7
    cr
    wcel
    #
    vk
    @0
    wral
    @10
    cM
    cN
    fzfi
    @1
    @11
    vk
    @0
    @0
    cr
    @6
    cF
    ffvelrn
    ralrimiva
    vx
    vk
    @0
    @7
    fimaxre3
    sylancr
    @1
    @5
    @9
    vx
    cr
    @1
    cF
    @0
    wfn
    @5
    @9
    wb
    @0
    cr
    cF
    ffn
    @4
    @8
    vy
    vk
    @0
    cF
    @2
    @7
    @3
    cle
    breq1
    ralrn
    syl
    rexbidv
    mpbird
end
