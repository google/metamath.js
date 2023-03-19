include "csrg.mm"
include "wcel.mm"
include "wa.mm"
include "cmnd.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "wf.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "srgmnd.mm"
include "jca.mm"
include "adantr.mm"
include "srgcl.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "3anass.mm"
include "srgdi.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "srgacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "srg0cl.mm"
include "srgrz.mm"
include "eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem srglmhm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume srglmhm.b: |- B = ( Base ` R )
  assume srglmhm.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint R x
  disjoint X x
  disjoint .x. x
  disjoint a b
  disjoint a x
  disjoint B a
  disjoint b x
  disjoint B b
  disjoint R a
  disjoint R b
  disjoint X a
  disjoint X b
  disjoint .x. a
  disjoint .x. b
  assert |- ( ( R e. SRing /\ X e. B ) -> ( x e. B |-> ( X .x. x ) ) e. ( R MndHom R ) )

  proof
    cR
    csrg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cR
    cmnd
    wcel
    #
    @3
    wa
    #
    cB
    cB
    vx
    cB
    cX
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @7
    cfv
    #
    @9
    @7
    cfv
    #
    @10
    @7
    cfv
    #
    @11
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
    cR
    c0g
    cfv
    #
    @7
    cfv
    #
    @19
    wceq
    #
    w3a
    @7
    cR
    cR
    cmhm
    co
    wcel
    @0
    @4
    @1
    @0
    @3
    @3
    cR
    srgmnd
    #
    @22
    jca
    adantr
    @2
    @8
    @18
    @21
    @2
    vx
    cB
    @6
    cB
    @7
    @0
    @1
    @5
    cB
    wcel
    @6
    cB
    wcel
    cB
    cR
    c.x
    cX
    @5
    srglmhm.b
    srglmhm.t
    srgcl
    3expa
    @7
    eqid
    #
    fmptd
    @2
    @17
    va
    vb
    cB
    cB
    @2
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    @12
    c.x
    co
    #
    cX
    @9
    c.x
    co
    #
    cX
    @10
    c.x
    co
    #
    @11
    co
    #
    @13
    @16
    @0
    @1
    @26
    @28
    @31
    wceq
    #
    @1
    @26
    wa
    @0
    @1
    @24
    @25
    w3a
    @32
    @1
    @24
    @25
    3anass
    cB
    @11
    cR
    c.x
    cX
    @9
    @10
    srglmhm.b
    @11
    eqid
    #
    srglmhm.t
    srgdi
    sylan2br
    anassrs
    @27
    @12
    cB
    wcel
    #
    @13
    @28
    wceq
    @0
    @26
    @34
    @1
    @0
    @24
    @25
    @34
    cB
    @11
    cR
    @9
    @10
    srglmhm.b
    @33
    srgacl
    3expb
    adantlr
    vx
    @12
    @6
    @28
    cB
    @7
    @5
    @12
    cX
    c.x
    oveq2
    @23
    cX
    @12
    c.x
    ovex
    fvmpt
    syl
    @26
    @16
    @31
    wceq
    @2
    @24
    @25
    @14
    @29
    @15
    @30
    @11
    vx
    @9
    @6
    @29
    cB
    @7
    @5
    @9
    cX
    c.x
    oveq2
    @23
    cX
    @9
    c.x
    ovex
    fvmpt
    vx
    @10
    @6
    @30
    cB
    @7
    @5
    @10
    cX
    c.x
    oveq2
    @23
    cX
    @10
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @2
    @20
    cX
    @19
    c.x
    co
    #
    @19
    @2
    @19
    cB
    wcel
    #
    @20
    @35
    wceq
    @0
    @36
    @1
    cB
    cR
    @19
    srglmhm.b
    @19
    eqid
    #
    srg0cl
    adantr
    vx
    @19
    @6
    @35
    cB
    @7
    @5
    @19
    cX
    c.x
    oveq2
    @23
    cX
    @19
    c.x
    ovex
    fvmpt
    syl
    cB
    cR
    c.x
    cX
    @19
    srglmhm.b
    srglmhm.t
    @37
    srgrz
    eqtrd
    3jca
    va
    vb
    cB
    cB
    @11
    @11
    cR
    cR
    @7
    @19
    @19
    srglmhm.b
    srglmhm.b
    @33
    @33
    @37
    @37
    ismhm
    sylanbrc
end
