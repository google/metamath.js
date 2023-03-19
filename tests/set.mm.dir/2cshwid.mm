include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "lencl.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "sylan.mm"
include "2cshw.mm"
include "mpd3an3.mm"
include "cc.mm"
include "zcn.mm"
include "nn0cnd.mm"
include "pncan3.mm"
include "syl2anr.mm"
include "oveq2d.mm"
include "cshwn.mm"
include "adantr.mm"
include "3eqtrd.mm"

theorem 2cshwid
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( ( W cyclShift N ) cyclShift ( ( # ` W ) - N ) ) = W )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    cW
    chash
    cfv
    #
    cN
    cmin
    co
    #
    ccsh
    co
    #
    cW
    cN
    @4
    caddc
    co
    #
    ccsh
    co
    #
    cW
    @3
    ccsh
    co
    #
    cW
    @0
    @1
    @4
    cz
    wcel
    #
    @5
    @7
    wceq
    @0
    @3
    cz
    wcel
    @1
    @9
    @0
    @3
    cV
    cW
    lencl
    #
    nn0zd
    @3
    cN
    zsubcl
    sylan
    cN
    @4
    cV
    cW
    2cshw
    mpd3an3
    @2
    @6
    @3
    cW
    ccsh
    @1
    cN
    cc
    wcel
    @3
    cc
    wcel
    @6
    @3
    wceq
    @0
    cN
    zcn
    @0
    @3
    @10
    nn0cnd
    cN
    @3
    pncan3
    syl2anr
    oveq2d
    @0
    @8
    cW
    wceq
    @1
    cV
    cW
    cshwn
    adantr
    3eqtrd
end
