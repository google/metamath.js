include "cv.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "clt.mm"
include "cfn.mm"
include "fzfi.mm"
include "fimaxre3.mm"
include "mpan.mm"
include "wi.mm"
include "wa.mm"
include "r19.26.mm"
include "c1.mm"
include "caddc.mm"
include "peano2re.mm"
include "ltp1.mm"
include "adantr.mm"
include "simpr.mm"
include "simpl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "expimpd.mm"
include "ralimdv.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "syl5bir.mm"
include "expd.mm"
include "impcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem fsequb
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vy: setvar y

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint k y
  disjoint x y
  disjoint F y
  disjoint M y
  disjoint N y
  assert |- ( A. k e. ( M ... N ) ( F ` k ) e. RR -> E. x e. RR A. k e. ( M ... N ) ( F ` k ) < x )

  proof
    vk
    cv
    cF
    cfv
    #
    cr
    wcel
    #
    vk
    cM
    cN
    cfz
    co
    #
    wral
    #
    @0
    vy
    cv
    #
    cle
    wbr
    #
    vk
    @2
    wral
    #
    vy
    cr
    wrex
    #
    @0
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @2
    wral
    #
    vx
    cr
    wrex
    #
    @2
    cfn
    wcel
    @3
    @7
    cM
    cN
    fzfi
    vy
    vk
    @2
    @0
    fimaxre3
    mpan
    @3
    @6
    @11
    vy
    cr
    @4
    cr
    wcel
    #
    @3
    @6
    @11
    wi
    @12
    @3
    @6
    @11
    @3
    @6
    wa
    @1
    @5
    wa
    #
    vk
    @2
    wral
    #
    @12
    @11
    @1
    @5
    vk
    @2
    r19.26
    @12
    @4
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @14
    @0
    @15
    clt
    wbr
    #
    vk
    @2
    wral
    #
    @11
    @4
    peano2re
    #
    @12
    @13
    @17
    vk
    @2
    @12
    @1
    @5
    @17
    @12
    @1
    wa
    #
    @5
    @4
    @15
    clt
    wbr
    #
    @17
    @12
    @21
    @1
    @4
    ltp1
    adantr
    @20
    @1
    @12
    @16
    @5
    @21
    wa
    @17
    wi
    @12
    @1
    simpr
    @12
    @1
    simpl
    @12
    @16
    @1
    @19
    adantr
    @0
    @4
    @15
    lelttr
    syl3anc
    mpan2d
    expimpd
    ralimdv
    @10
    @18
    vx
    @15
    cr
    @8
    @15
    wceq
    @9
    @17
    vk
    @2
    @8
    @15
    @0
    clt
    breq2
    ralbidv
    rspcev
    syl6an
    syl5bir
    expd
    impcom
    rexlimdva
    mpd
end
