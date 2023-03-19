include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cintop.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-intop.mm"
include "a1i.mm"
include "simpr.mm"
include "simpl.mm"
include "sqxpeqd.mm"
include "oveq12d.mm"
include "adantl.mm"
include "elex.mm"
include "adantr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem intopval
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. V /\ N e. W ) -> ( M intOp N ) = ( N ^m ( M X. M ) ) )

  proof
    cM
    cV
    wcel
    #
    cN
    cW
    wcel
    #
    wa
    #
    vm
    vn
    cM
    cN
    cvv
    cvv
    vn
    cv
    #
    vm
    cv
    #
    @4
    cxp
    #
    cmap
    co
    #
    cN
    cM
    cM
    cxp
    #
    cmap
    co
    #
    cintop
    cvv
    cintop
    vm
    vn
    cvv
    cvv
    @6
    cmpt2
    wceq
    @2
    vm
    vn
    df-intop
    a1i
    @4
    cM
    wceq
    #
    @3
    cN
    wceq
    #
    wa
    #
    @6
    @8
    wceq
    @2
    @11
    @3
    cN
    @5
    @7
    cmap
    @9
    @10
    simpr
    @11
    @4
    cM
    @9
    @10
    simpl
    sqxpeqd
    oveq12d
    adantl
    @0
    cM
    cvv
    wcel
    @1
    cM
    cV
    elex
    adantr
    @1
    cN
    cvv
    wcel
    @0
    cN
    cW
    elex
    adantl
    @2
    cN
    @7
    cmap
    ovexd
    ovmpt2d
end
