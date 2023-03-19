include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "cpfx.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-pfx.mm"
include "a1i.mm"
include "simpl.mm"
include "opeq2.mm"
include "adantl.mm"
include "oveq12d.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem pfxval
  let cS: class S
  let cL: class L
  let cV: class V
  let vl: setvar l
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. V /\ L e. NN0 ) -> ( S prefix L ) = ( S substr <. 0 , L >. ) )

  proof
    cS
    cV
    wcel
    #
    cL
    cn0
    wcel
    #
    wa
    #
    vs
    vl
    cS
    cL
    cvv
    cn0
    vs
    cv
    #
    cc0
    vl
    cv
    #
    cop
    #
    csubstr
    co
    #
    cS
    cc0
    cL
    cop
    #
    csubstr
    co
    #
    cpfx
    cvv
    cpfx
    vs
    vl
    cvv
    cn0
    @6
    cmpt2
    wceq
    @2
    vs
    vl
    df-pfx
    a1i
    @3
    cS
    wceq
    #
    @4
    cL
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
    cS
    @5
    @7
    csubstr
    @9
    @10
    simpl
    @10
    @5
    @7
    wceq
    @9
    @4
    cL
    cc0
    opeq2
    adantl
    oveq12d
    adantl
    @0
    cS
    cvv
    wcel
    @1
    cS
    cV
    elex
    adantr
    @0
    @1
    simpr
    @2
    cS
    @7
    csubstr
    ovexd
    ovmpt2d
end
