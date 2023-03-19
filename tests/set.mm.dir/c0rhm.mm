include "crg.mm"
include "wcel.mm"
include "cnzr.mm"
include "cdif.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "eldifi.mm"
include "anim2i.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "c0ghm.mm"
include "syl2an.mm"
include "cur.mm"
include "cmpt.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "0ring1eq0.mm"
include "eqcomd.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "syl5eq.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "c0mhm.mm"
include "eqeltrd.mm"
include "jca.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem c0rhm
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
  assert |- ( ( S e. Ring /\ T e. ( Ring \ NzRing ) ) -> H e. ( S RingHom T ) )

  proof
    cS
    crg
    wcel
    #
    cT
    crg
    cnzr
    cdif
    wcel
    #
    wa
    #
    @0
    cT
    crg
    wcel
    #
    wa
    cH
    cS
    cT
    cghm
    co
    wcel
    #
    cH
    cS
    cmgp
    cfv
    #
    cT
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    cH
    cS
    cT
    crh
    co
    wcel
    @1
    @3
    @0
    cT
    crg
    cnzr
    eldifi
    #
    anim2i
    @2
    @4
    @8
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    #
    @4
    @1
    cS
    ringgrp
    @1
    @3
    @10
    @9
    cT
    ringgrp
    syl
    vx
    cB
    cS
    cT
    cH
    c.0
    c0mhm.b
    c0mhm.0
    c0mhm.h
    c0ghm
    syl2an
    @2
    cH
    vx
    cB
    cT
    cur
    cfv
    #
    cmpt
    #
    @7
    @2
    cH
    vx
    cB
    c.0
    cmpt
    #
    @12
    c0mhm.h
    @1
    @13
    @12
    wceq
    @0
    @1
    vx
    cB
    c.0
    @11
    @1
    @11
    c.0
    cT
    cbs
    cfv
    #
    cT
    @11
    c.0
    @14
    eqid
    c0mhm.0
    @11
    eqid
    #
    0ring1eq0
    eqcomd
    mpteq2dv
    adantl
    syl5eq
    @0
    @5
    cmnd
    wcel
    @6
    cmnd
    wcel
    #
    @12
    @7
    wcel
    @1
    cS
    @5
    @5
    eqid
    #
    ringmgp
    @1
    @3
    @16
    @9
    cT
    @6
    @6
    eqid
    #
    ringmgp
    syl
    vx
    cB
    @5
    @6
    @12
    @11
    cB
    cS
    @5
    @17
    c0mhm.b
    mgpbas
    cT
    @11
    @6
    @18
    @15
    ringidval
    @12
    eqid
    c0mhm
    syl2an
    eqeltrd
    jca
    cS
    cT
    cH
    @5
    @6
    @17
    @18
    isrhm
    sylanbrc
end
