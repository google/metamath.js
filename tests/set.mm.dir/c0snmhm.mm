include "cmnd.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cmgmhm.mm"
include "co.mm"
include "cfv.mm"
include "cmhm.mm"
include "pm3.22.mm"
include "3adant3.mm"
include "cmgm.mm"
include "chash.mm"
include "c1.mm"
include "simp1.mm"
include "mndmgm.mm"
include "3ad2ant2.mm"
include "fveq2.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "3ad2ant3.mm"
include "c0snmgmhm.mm"
include "syl3anc.mm"
include "cbs.mm"
include "cmpt.mm"
include "a1i.mm"
include "cv.mm"
include "eqidd.mm"
include "snid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "eqid.mm"
include "mndidcl.mm"
include "3ad2ant1.mm"
include "fvmptd.mm"
include "jca.mm"
include "cplusg.mm"
include "ismhm0.mm"
include "sylanbrc.mm"

theorem c0snmhm
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
  assert |- ( ( S e. Mnd /\ T e. Mnd /\ B = { Z } ) -> H e. ( T MndHom S ) )

  proof
    cS
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
    cB
    cZ
    csn
    #
    wceq
    #
    w3a
    #
    @1
    @0
    wa
    #
    cH
    cT
    cS
    cmgmhm
    co
    wcel
    #
    cZ
    cH
    cfv
    c.0
    wceq
    #
    wa
    cH
    cT
    cS
    cmhm
    co
    wcel
    @0
    @1
    @5
    @3
    @0
    @1
    pm3.22
    3adant3
    @4
    @6
    @7
    @4
    @0
    cT
    cmgm
    wcel
    #
    cB
    chash
    cfv
    #
    c1
    wceq
    #
    @6
    @0
    @1
    @3
    simp1
    @1
    @0
    @8
    @3
    cT
    mndmgm
    3ad2ant2
    @3
    @0
    @10
    @1
    @3
    @9
    @2
    chash
    cfv
    #
    c1
    cB
    @2
    chash
    fveq2
    cZ
    cvv
    wcel
    @11
    c1
    wceq
    cZ
    cT
    c0g
    cfv
    cvv
    c0snmhm.z
    cT
    c0g
    fvex
    eqeltri
    #
    cZ
    cvv
    hashsng
    ax-mp
    syl6eq
    3ad2ant3
    vx
    cB
    cS
    cT
    cH
    c.0
    zrrhm.b
    zrrhm.0
    zrrhm.h
    c0snmgmhm
    syl3anc
    @4
    vx
    cZ
    c.0
    c.0
    cB
    cH
    cS
    cbs
    cfv
    #
    cH
    vx
    cB
    c.0
    cmpt
    wceq
    @4
    zrrhm.h
    a1i
    @4
    vx
    cv
    cZ
    wceq
    wa
    c.0
    eqidd
    @3
    @0
    cZ
    cB
    wcel
    #
    @1
    @3
    @14
    cZ
    @2
    wcel
    cZ
    @12
    snid
    cB
    @2
    cZ
    eleq2
    mpbiri
    3ad2ant3
    @0
    @1
    c.0
    @13
    wcel
    @3
    @13
    cS
    c.0
    @13
    eqid
    #
    zrrhm.0
    mndidcl
    3ad2ant1
    fvmptd
    jca
    cB
    @13
    cT
    cplusg
    cfv
    #
    cS
    cplusg
    cfv
    #
    cT
    cS
    cH
    c.0
    cZ
    zrrhm.b
    @15
    @16
    eqid
    @17
    eqid
    c0snmhm.z
    zrrhm.0
    ismhm0
    sylanbrc
end
