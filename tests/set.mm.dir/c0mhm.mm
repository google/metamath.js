include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
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
include "weq.mm"
include "eqidd.mm"
include "simprl.mm"
include "fvmptd.mm"
include "simprr.mm"
include "oveq12d.mm"
include "mndcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylibr.mm"

theorem c0mhm
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
  assert |- ( ( S e. Mnd /\ T e. Mnd ) -> H e. ( S MndHom T ) )

  proof
    cS
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
    wa
    #
    @2
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
    @5
    cH
    cfv
    #
    @6
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
    cS
    c0g
    cfv
    #
    cH
    cfv
    c.0
    wceq
    #
    w3a
    #
    wa
    cH
    cS
    cT
    cmhm
    co
    wcel
    @2
    @18
    @2
    @4
    @15
    @17
    @2
    vx
    cB
    c.0
    @3
    cH
    @2
    c.0
    @3
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    @1
    @19
    @0
    @3
    cT
    c.0
    @3
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
    @14
    va
    vb
    cB
    cB
    @2
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    c.0
    c.0
    @12
    co
    #
    c.0
    @13
    @9
    @2
    @28
    c.0
    wceq
    #
    @26
    @2
    @1
    @19
    wa
    #
    @29
    @1
    @30
    @0
    @1
    @19
    @22
    ancli
    adantl
    @3
    @12
    cT
    c.0
    c.0
    @21
    @12
    eqid
    #
    c0mhm.0
    mndlid
    syl
    adantr
    @27
    @10
    c.0
    @11
    c.0
    @12
    @27
    vx
    @5
    c.0
    c.0
    cB
    cH
    @3
    cH
    vx
    cB
    c.0
    cmpt
    wceq
    #
    @27
    c0mhm.h
    a1i
    #
    @27
    vx
    va
    weq
    wa
    c.0
    eqidd
    @2
    @24
    @25
    simprl
    @2
    @19
    @26
    @23
    adantr
    #
    fvmptd
    @27
    vx
    @6
    c.0
    c.0
    cB
    cH
    @3
    @33
    @27
    vx
    vb
    weq
    wa
    c.0
    eqidd
    @2
    @24
    @25
    simprr
    @34
    fvmptd
    oveq12d
    @27
    vx
    @8
    c.0
    c.0
    cB
    cH
    @3
    @33
    @27
    @20
    @8
    wceq
    wa
    c.0
    eqidd
    @0
    @26
    @8
    cB
    wcel
    #
    @1
    @0
    @24
    @25
    @35
    cB
    @7
    cS
    @5
    @6
    c0mhm.b
    @7
    eqid
    #
    mndcl
    3expb
    adantlr
    @34
    fvmptd
    3eqtr4rd
    ralrimivva
    @2
    vx
    @16
    c.0
    c.0
    cB
    cH
    @3
    @32
    @2
    c0mhm.h
    a1i
    @2
    @20
    @16
    wceq
    wa
    c.0
    eqidd
    @0
    @16
    cB
    wcel
    @1
    cB
    cS
    @16
    c0mhm.b
    @16
    eqid
    #
    mndidcl
    adantr
    @23
    fvmptd
    3jca
    ancli
    va
    vb
    cB
    @3
    @7
    @12
    cS
    cT
    cH
    c.0
    @16
    c0mhm.b
    @21
    @36
    @31
    @37
    c0mhm.0
    ismhm
    sylibr
end
