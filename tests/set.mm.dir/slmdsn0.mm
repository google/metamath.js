include "cslmd.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "csrg.mm"
include "cmnd.mm"
include "slmdsrg.mm"
include "srgmnd.mm"
include "eqid.mm"
include "mndidcl.mm"
include "3syl.mm"
include "ne0i.mm"
include "syl.mm"

theorem slmdsn0
  let cB: class B
  let cF: class F
  let cW: class W
  assume slmdsn0.f: |- F = ( Scalar ` W )
  assume slmdsn0.b: |- B = ( Base ` F )


  assert |- ( W e. SLMod -> B =/= (/) )

  proof
    cW
    cslmd
    wcel
    #
    cF
    c0g
    cfv
    #
    cB
    wcel
    #
    cB
    c0
    wne
    @0
    cF
    csrg
    wcel
    cF
    cmnd
    wcel
    @2
    cF
    cW
    slmdsn0.f
    slmdsrg
    cF
    srgmnd
    cB
    cF
    @1
    slmdsn0.b
    @1
    eqid
    mndidcl
    3syl
    cB
    @1
    ne0i
    syl
end
