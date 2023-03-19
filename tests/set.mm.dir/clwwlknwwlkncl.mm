include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cn.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
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
include "cs1.mm"
include "cconcat.mm"
include "cwwlksn.mm"
include "crab.mm"
include "clwwlknnn.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "w3a.mm"
include "clwwlknp.mm"
include "3simpc.mm"
include "syl.mm"
include "clwwlkel.mm"
include "syl3anc.mm"

theorem clwwlknwwlkncl
  let vw: setvar w
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( W e. ( N ClWWalksN G ) -> ( W ++ <" ( W ` 0 ) "> ) e. { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) } )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cN
    cn
    wcel
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    cW
    chash
    cfv
    cN
    wceq
    wa
    #
    vi
    cv
    #
    cW
    cfv
    @3
    c1
    caddc
    co
    cW
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
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    #
    cpr
    @4
    wcel
    #
    wa
    #
    cW
    @6
    cs1
    cconcat
    co
    vw
    cv
    #
    clsw
    cfv
    cc0
    @9
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
    cG
    cN
    cW
    clwwlknnn
    cG
    cN
    @1
    cW
    @1
    eqid
    #
    clwwlknbp
    @0
    @2
    @5
    @7
    w3a
    @8
    vi
    @4
    cG
    cN
    @1
    cW
    @11
    @4
    eqid
    clwwlknp
    @2
    @5
    @7
    3simpc
    syl
    vw
    @10
    cW
    vi
    cG
    cN
    @10
    eqid
    clwwlkel
    syl3anc
end
