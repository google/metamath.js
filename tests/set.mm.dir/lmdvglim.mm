include "cpnf.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "cr.mm"
include "lmdvg.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cicc.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "lmxrge0.mm"
include "mpbird.mm"

theorem lmdvglim
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let vj: setvar j
  let vx: setvar x
  assume lmdvglim.j: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
  assume lmdvglim.1: |- ( ph -> F : NN --> ( 0 [,) +oo ) )
  assume lmdvglim.2: |- ( ( ph /\ k e. NN ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) )
  assume lmdvglim.3: |- ( ph -> -. F e. dom ~~> )

  disjoint F k
  disjoint J k
  disjoint k ph
  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F x
  disjoint J x
  disjoint j ph
  disjoint ph x
  assert |- ( ph -> F ( ~~>t ` J ) +oo )

  proof
    wph
    cF
    cpnf
    cJ
    clm
    cfv
    wbr
    vx
    cv
    vk
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cn
    wrex
    vx
    cr
    wral
    wph
    vx
    vj
    vk
    cF
    lmdvglim.1
    lmdvglim.2
    lmdvglim.3
    lmdvg
    wph
    vx
    @1
    vj
    vk
    cF
    cJ
    lmdvglim.j
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    @2
    cc0
    cpnf
    cicc
    co
    #
    wss
    cn
    @3
    cF
    wf
    lmdvglim.1
    cc0
    cpnf
    icossicc
    cn
    @2
    @3
    cF
    fss
    sylancl
    wph
    @0
    cn
    wcel
    wa
    @1
    eqidd
    lmxrge0
    mpbird
end
