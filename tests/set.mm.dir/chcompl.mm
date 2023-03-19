include "cch.mm"
include "wcel.mm"
include "ccau.mm"
include "cn.mm"
include "wf.mm"
include "cv.mm"
include "chli.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "csh.mm"
include "isch3.mm"
include "simprbi.mm"
include "wceq.mm"
include "feq1.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl.mm"
include "3imp.mm"

theorem chcompl
  let vx: setvar x
  let cF: class F
  let cH: class H
  let vf: setvar f

  disjoint H x
  disjoint F x
  disjoint f x
  disjoint H f
  disjoint F f
  assert |- ( ( H e. CH /\ F e. Cauchy /\ F : NN --> H ) -> E. x e. H F ~~>v x )

  proof
    cH
    cch
    wcel
    #
    cF
    ccau
    wcel
    #
    cn
    cH
    cF
    wf
    #
    cF
    vx
    cv
    #
    chli
    wbr
    #
    vx
    cH
    wrex
    #
    @0
    cn
    cH
    vf
    cv
    #
    wf
    #
    @6
    @3
    chli
    wbr
    #
    vx
    cH
    wrex
    #
    wi
    #
    vf
    ccau
    wral
    #
    @1
    @2
    @5
    wi
    #
    wi
    @0
    cH
    csh
    wcel
    @11
    vx
    vf
    cH
    isch3
    simprbi
    @10
    @12
    vf
    cF
    ccau
    @6
    cF
    wceq
    #
    @7
    @2
    @9
    @5
    cn
    cH
    @6
    cF
    feq1
    @13
    @8
    @4
    vx
    cH
    @6
    cF
    @3
    chli
    breq1
    rexbidv
    imbi12d
    rspccv
    syl
    3imp
end
