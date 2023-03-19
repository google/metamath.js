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
include "3com23.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "3anrot.mm"
include "3anass.mm"
include "bitr3i.mm"
include "srgdir.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "srgacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "srg0cl.mm"
include "srglz.mm"
include "eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem srgrmhm
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
  assert |- ( ( R e. SRing /\ X e. B ) -> ( x e. B |-> ( x .x. X ) ) e. ( R MndHom R ) )

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
    vx
    cv
    #
    cX
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
    #
    @6
    cB
    wcel
    #
    @0
    @23
    @1
    @24
    cB
    cR
    c.x
    @5
    cX
    srglmhm.b
    srglmhm.t
    srgcl
    3com23
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
    @12
    cX
    c.x
    co
    #
    @9
    cX
    c.x
    co
    #
    @10
    cX
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
    @28
    @30
    @33
    wceq
    #
    @1
    @28
    wa
    #
    @0
    @26
    @27
    @1
    w3a
    #
    @34
    @36
    @1
    @26
    @27
    w3a
    @35
    @1
    @26
    @27
    3anrot
    @1
    @26
    @27
    3anass
    bitr3i
    cB
    @11
    cR
    c.x
    @9
    @10
    cX
    srglmhm.b
    @11
    eqid
    #
    srglmhm.t
    srgdir
    sylan2br
    anassrs
    @29
    @12
    cB
    wcel
    #
    @13
    @30
    wceq
    @0
    @28
    @38
    @1
    @0
    @26
    @27
    @38
    cB
    @11
    cR
    @9
    @10
    srglmhm.b
    @37
    srgacl
    3expb
    adantlr
    vx
    @12
    @6
    @30
    cB
    @7
    @5
    @12
    cX
    c.x
    oveq1
    @25
    @12
    cX
    c.x
    ovex
    fvmpt
    syl
    @28
    @16
    @33
    wceq
    @2
    @26
    @27
    @14
    @31
    @15
    @32
    @11
    vx
    @9
    @6
    @31
    cB
    @7
    @5
    @9
    cX
    c.x
    oveq1
    @25
    @9
    cX
    c.x
    ovex
    fvmpt
    vx
    @10
    @6
    @32
    cB
    @7
    @5
    @10
    cX
    c.x
    oveq1
    @25
    @10
    cX
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @2
    @20
    @19
    cX
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
    @39
    wceq
    @0
    @40
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
    @39
    cB
    @7
    @5
    @19
    cX
    c.x
    oveq1
    @25
    @19
    cX
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
    @41
    srglz
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
    @37
    @37
    @41
    @41
    ismhm
    sylanbrc
end
