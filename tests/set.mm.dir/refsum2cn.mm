include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfif.mm"
include "nfmpt.mm"
include "eqid.mm"
include "refsum2cnlem1.mm"

theorem refsum2cn
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vk: setvar k
  assume refsum2cn.1: |- F/_ x F
  assume refsum2cn.2: |- F/_ x G
  assume refsum2cn.3: |- F/ x ph
  assume refsum2cn.4: |- K = ( topGen ` ran (,) )
  assume refsum2cn.5: |- ( ph -> J e. ( TopOn ` X ) )
  assume refsum2cn.6: |- ( ph -> F e. ( J Cn K ) )
  assume refsum2cn.7: |- ( ph -> G e. ( J Cn K ) )

  disjoint J x
  disjoint K x
  disjoint X x
  disjoint k x
  disjoint J k
  disjoint F k
  disjoint G k
  disjoint K k
  disjoint X k
  disjoint k ph
  assert |- ( ph -> ( x e. X |-> ( ( F ` x ) + ( G ` x ) ) ) e. ( J Cn K ) )

  proof
    wph
    vx
    vk
    c1
    c2
    cpr
    #
    vk
    cv
    c1
    wceq
    #
    cF
    cG
    cif
    #
    cmpt
    #
    vk
    cF
    cG
    cJ
    cK
    cX
    vx
    vk
    @0
    @2
    vx
    @0
    nfcv
    @1
    vx
    cF
    cG
    @1
    vx
    nfv
    refsum2cn.1
    refsum2cn.2
    nfif
    nfmpt
    refsum2cn.1
    refsum2cn.2
    refsum2cn.3
    @3
    eqid
    refsum2cn.4
    refsum2cn.5
    refsum2cn.6
    refsum2cn.7
    refsum2cnlem1
end
