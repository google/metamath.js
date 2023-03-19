include "cmgm.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cmgmhm.mm"
include "mndmgm.mm"
include "anim2i.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantl.mm"
include "adantr.mm"
include "fmptd.mm"
include "ancli.mm"
include "mndlid.mm"
include "syl.mm"
include "cmpt.mm"
include "a1i.mm"
include "eqidd.mm"
include "simprl.mm"
include "fvmptd.mm"
include "simprr.mm"
include "oveq12d.mm"
include "mgmcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem c0mgm
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
  assert |- ( ( S e. Mgm /\ T e. Mnd ) -> H e. ( S MgmHom T ) )

  proof
    cS
    cmgm
    wcel
    #
    cT
    cmnd
    wcel
    #
    wa
    #
    @0
    cT
    cmgm
    wcel
    #
    wa
    cB
    cT
    cbs
    cfv
    #
    cH
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    cH
    cfv
    #
    @6
    cH
    cfv
    #
    @7
    cH
    cfv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    cH
    cS
    cT
    cmgmhm
    co
    wcel
    @1
    @3
    @0
    cT
    mndmgm
    anim2i
    @2
    @5
    @16
    @2
    vx
    cB
    c.0
    @4
    cH
    @2
    c.0
    @4
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    @1
    @17
    @0
    @4
    cT
    c.0
    @4
    eqid
    #
    c0mhm.0
    mndidcl
    #
    adantl
    #
    adantr
    c0mhm.h
    fmptd
    @2
    @15
    va
    vb
    cB
    cB
    @2
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    wa
    #
    c.0
    c.0
    @13
    co
    #
    c.0
    @14
    @10
    @2
    @26
    c.0
    wceq
    #
    @24
    @2
    @1
    @17
    wa
    #
    @27
    @1
    @28
    @0
    @1
    @17
    @20
    ancli
    adantl
    @4
    @13
    cT
    c.0
    c.0
    @19
    @13
    eqid
    #
    c0mhm.0
    mndlid
    syl
    adantr
    @25
    @11
    c.0
    @12
    c.0
    @13
    @25
    vx
    @6
    c.0
    c.0
    cB
    cH
    @4
    cH
    vx
    cB
    c.0
    cmpt
    wceq
    @25
    c0mhm.h
    a1i
    #
    @25
    @18
    @6
    wceq
    wa
    c.0
    eqidd
    @2
    @22
    @23
    simprl
    @2
    @17
    @24
    @21
    adantr
    #
    fvmptd
    @25
    vx
    @7
    c.0
    c.0
    cB
    cH
    @4
    @30
    @25
    @18
    @7
    wceq
    wa
    c.0
    eqidd
    @2
    @22
    @23
    simprr
    @31
    fvmptd
    oveq12d
    @25
    vx
    @9
    c.0
    c.0
    cB
    cH
    @4
    @30
    @25
    @18
    @9
    wceq
    wa
    c.0
    eqidd
    @0
    @24
    @9
    cB
    wcel
    #
    @1
    @0
    @22
    @23
    @32
    cB
    cS
    @6
    @7
    @8
    c0mhm.b
    @8
    eqid
    #
    mgmcl
    3expb
    adantlr
    @31
    fvmptd
    3eqtr4rd
    ralrimivva
    jca
    va
    vb
    cB
    @4
    @8
    @13
    cS
    cT
    cH
    c0mhm.b
    @19
    @33
    @29
    ismgmhm
    sylanbrc
end
