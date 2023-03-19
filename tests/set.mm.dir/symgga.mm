include "wcel.mm"
include "cgrp.mm"
include "cid.mm"
include "cres.mm"
include "cghm.mm"
include "co.mm"
include "cga.mm"
include "symggrp.mm"
include "idghm.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "wa.mm"
include "wceq.mm"
include "fvresi.mm"
include "adantr.mm"
include "fveq1d.mm"
include "mpt2eq3ia.mm"
include "eqtr4i.mm"
include "lactghmga.mm"
include "3syl.mm"

theorem symgga
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  assume symgga.g: |- G = ( SymGrp ` X )
  assume symgga.b: |- B = ( Base ` G )
  assume symgga.f: |- F = ( f e. B , x e. X |-> ( f ` x ) )

  disjoint f x
  disjoint B f
  disjoint B x
  disjoint G f
  disjoint G x
  disjoint V f
  disjoint V x
  disjoint X f
  disjoint X x
  assert |- ( X e. V -> F e. ( G GrpAct X ) )

  proof
    cX
    cV
    wcel
    cG
    cgrp
    wcel
    cid
    cB
    cres
    #
    cG
    cG
    cghm
    co
    wcel
    cF
    cG
    cX
    cga
    co
    wcel
    cX
    cG
    cV
    symgga.g
    symggrp
    cB
    cG
    symgga.b
    idghm
    vf
    vx
    cF
    @0
    cG
    cG
    cB
    cX
    symgga.b
    symgga.g
    cF
    vf
    vx
    cB
    cX
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    cmpt2
    vf
    vx
    cB
    cX
    @1
    @2
    @0
    cfv
    #
    cfv
    #
    cmpt2
    symgga.f
    vf
    vx
    cB
    cX
    @5
    @3
    @2
    cB
    wcel
    #
    @1
    cX
    wcel
    #
    wa
    @1
    @4
    @2
    @6
    @4
    @2
    wceq
    @7
    cB
    @2
    fvresi
    adantr
    fveq1d
    mpt2eq3ia
    eqtr4i
    lactghmga
    3syl
end
