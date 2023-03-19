include "cn.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "cwwlksn.mm"
include "crab.mm"
include "simpr.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "adantr.mm"
include "clwwlknp.mm"
include "3simpc.mm"
include "syl.mm"
include "3jca.mm"
include "ancoms.mm"
include "clwwlkel.mm"

theorem clwwlknwwlknclOLD
  let vw: setvar w
  let cP: class P
  let cG: class G
  let cN: class N
  let vi: setvar i

  disjoint G w
  disjoint N w
  disjoint P w
  disjoint G i
  disjoint N i
  disjoint P i
  assert |- ( ( N e. NN /\ P e. ( N ClWWalksN G ) ) -> ( P ++ <" ( P ` 0 ) "> ) e. { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) } )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    wa
    @0
    cP
    cG
    cvtx
    cfv
    #
    cword
    wcel
    cP
    chash
    cfv
    cN
    wceq
    wa
    #
    vi
    cv
    #
    cP
    cfv
    @4
    c1
    caddc
    co
    cP
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cP
    clsw
    cfv
    cc0
    cP
    cfv
    #
    cpr
    @5
    wcel
    #
    wa
    #
    w3a
    #
    cP
    @7
    cs1
    cconcat
    co
    vw
    cv
    #
    clsw
    cfv
    cc0
    @11
    cfv
    wceq
    vw
    cN
    cG
    cwwlksn
    co
    crab
    #
    wcel
    @1
    @0
    @10
    @1
    @0
    wa
    @0
    @3
    @9
    @1
    @0
    simpr
    @1
    @3
    @0
    cG
    cN
    @2
    cP
    @2
    eqid
    #
    clwwlknbp
    adantr
    @1
    @9
    @0
    @1
    @3
    @6
    @8
    w3a
    @9
    vi
    @5
    cG
    cN
    @2
    cP
    @13
    @5
    eqid
    clwwlknp
    @3
    @6
    @8
    3simpc
    syl
    adantr
    3jca
    ancoms
    vw
    @12
    cP
    vi
    cG
    cN
    @12
    eqid
    clwwlkel
    syl
end
