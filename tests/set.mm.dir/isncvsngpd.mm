include "ccvs.mm"
include "wcel.mm"
include "cngp.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cnvc.mm"
include "cin.mm"
include "ralrimivva.mm"
include "isncvsngp.mm"
include "syl3anbrc.mm"

theorem isncvsngpd
  let wph: wff ph
  let vx: setvar x
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume isncvsngp.v: |- V = ( Base ` W )
  assume isncvsngp.n: |- N = ( norm ` W )
  assume isncvsngp.s: |- .x. = ( .s ` W )
  assume isncvsngp.f: |- F = ( Scalar ` W )
  assume isncvsngp.k: |- K = ( Base ` F )
  assume isncvsngpd.v: |- ( ph -> W e. CVec )
  assume isncvsngpd.g: |- ( ph -> W e. NrmGrp )
  assume isncvsngpd.t: |- ( ( ph /\ ( x e. V /\ k e. K ) ) -> ( N ` ( k .x. x ) ) = ( ( abs ` k ) x. ( N ` x ) ) )

  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint k x
  disjoint K k
  disjoint K x
  disjoint N k
  disjoint N x
  disjoint V k
  disjoint V x
  disjoint W k
  disjoint W x
  disjoint .x. k
  disjoint .x. x
  assert |- ( ph -> W e. ( NrmVec i^i CVec ) )

  proof
    wph
    cW
    ccvs
    wcel
    cW
    cngp
    wcel
    vk
    cv
    #
    vx
    cv
    #
    c.x
    co
    cN
    cfv
    @0
    cabs
    cfv
    @1
    cN
    cfv
    cmul
    co
    wceq
    #
    vk
    cK
    wral
    vx
    cV
    wral
    cW
    cnvc
    ccvs
    cin
    wcel
    isncvsngpd.v
    isncvsngpd.g
    wph
    @2
    vx
    vk
    cV
    cK
    isncvsngpd.t
    ralrimivva
    vx
    c.x
    vk
    cF
    cK
    cN
    cV
    cW
    isncvsngp.v
    isncvsngp.n
    isncvsngp.s
    isncvsngp.f
    isncvsngp.k
    isncvsngp
    syl3anbrc
end
