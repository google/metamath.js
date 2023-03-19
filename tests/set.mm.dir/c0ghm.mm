include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmhm.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "anim12i.mm"
include "c0mhm.mm"
include "syl.mm"
include "ghmmhmb.mm"
include "eleq2d.mm"
include "mpbird.mm"

theorem c0ghm
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume c0mhm.b: |- B = ( Base ` S )
  assume c0mhm.0: |- .0. = ( 0g ` T )
  assume c0mhm.h: |- H = ( x e. B |-> .0. )

  disjoint B x
  disjoint S x
  disjoint T x
  disjoint .0. x
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint H a
  disjoint H b
  disjoint S a
  disjoint S b
  disjoint T a
  disjoint T b
  disjoint k x
  assert |- ( ( S e. Grp /\ T e. Grp ) -> H e. ( S GrpHom T ) )

  proof
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    wa
    #
    cH
    cS
    cT
    cghm
    co
    #
    wcel
    cH
    cS
    cT
    cmhm
    co
    #
    wcel
    #
    @2
    cS
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
    wa
    @5
    @0
    @6
    @1
    @7
    cS
    grpmnd
    cT
    grpmnd
    anim12i
    vx
    cB
    cS
    cT
    cH
    c.0
    c0mhm.b
    c0mhm.0
    c0mhm.h
    c0mhm
    syl
    @2
    @3
    @4
    cH
    cS
    cT
    ghmmhmb
    eleq2d
    mpbird
end
