include "cgrp.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "cghm.mm"
include "co.mm"
include "cmhm.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "id.mm"
include "c0snmhm.mm"
include "syl3an.mm"
include "wb.mm"
include "wa.mm"
include "ghmmhmb.mm"
include "eleq2d.mm"
include "ancoms.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem c0snghm
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.0: class .0.
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume zrrhm.b: |- B = ( Base ` T )
  assume zrrhm.0: |- .0. = ( 0g ` S )
  assume zrrhm.h: |- H = ( x e. B |-> .0. )
  assume c0snmhm.z: |- Z = ( 0g ` T )

  disjoint Z x
  disjoint B x
  disjoint S x
  disjoint T x
  disjoint .0. x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint b c
  disjoint b x
  disjoint c x
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint k x
  assert |- ( ( S e. Grp /\ T e. Grp /\ B = { Z } ) -> H e. ( T GrpHom S ) )

  proof
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    cB
    cZ
    csn
    wceq
    #
    w3a
    cH
    cT
    cS
    cghm
    co
    #
    wcel
    #
    cH
    cT
    cS
    cmhm
    co
    #
    wcel
    #
    @0
    cS
    cmnd
    wcel
    @1
    cT
    cmnd
    wcel
    @2
    @2
    @6
    cS
    grpmnd
    cT
    grpmnd
    @2
    id
    vx
    cB
    cS
    cT
    cH
    c.0
    cZ
    zrrhm.b
    zrrhm.0
    zrrhm.h
    c0snmhm.z
    c0snmhm
    syl3an
    @0
    @1
    @4
    @6
    wb
    #
    @2
    @1
    @0
    @7
    @1
    @0
    wa
    @3
    @5
    cH
    cT
    cS
    ghmmhmb
    eleq2d
    ancoms
    3adant3
    mpbird
end
