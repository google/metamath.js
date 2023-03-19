include "ccmn.mm"
include "wcel.mm"
include "cn0.mm"
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
include "cmnmnd.mm"
include "adantr.mm"
include "jca.mm"
include "mulgnn0cl.mm"
include "syl3an1.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "3anass.mm"
include "mulgnn0di.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "mndidcl.mm"
include "3syl.mm"
include "mulgnn0z.mm"
include "eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem mulgmhm
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume mulgmhm.b: |- B = ( Base ` G )
  assume mulgmhm.m: |- .x. = ( .g ` G )

  disjoint B x
  disjoint G x
  disjoint M x
  disjoint .x. x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint M y
  disjoint M z
  disjoint .x. y
  disjoint .x. z
  assert |- ( ( G e. CMnd /\ M e. NN0 ) -> ( x e. B |-> ( M .x. x ) ) e. ( G MndHom G ) )

  proof
    cG
    ccmn
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cG
    cmnd
    wcel
    #
    @3
    wa
    cB
    cB
    vx
    cB
    cM
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
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @6
    cfv
    #
    @8
    @6
    cfv
    #
    @9
    @6
    cfv
    #
    @10
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    cG
    c0g
    cfv
    #
    @6
    cfv
    #
    @18
    wceq
    #
    w3a
    @6
    cG
    cG
    cmhm
    co
    wcel
    @2
    @3
    @3
    @0
    @3
    @1
    cG
    cmnmnd
    #
    adantr
    #
    @22
    jca
    @2
    @7
    @17
    @20
    @2
    vx
    cB
    @5
    cB
    @6
    @0
    @1
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @0
    @3
    @1
    @23
    @24
    @21
    cB
    c.x
    cG
    cM
    @4
    mulgmhm.b
    mulgmhm.m
    mulgnn0cl
    syl3an1
    3expa
    @6
    eqid
    #
    fmptd
    @2
    @16
    vy
    vz
    cB
    cB
    @2
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    wa
    #
    wa
    #
    cM
    @11
    c.x
    co
    #
    cM
    @8
    c.x
    co
    #
    cM
    @9
    c.x
    co
    #
    @10
    co
    #
    @12
    @15
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
    @0
    @1
    @26
    @27
    w3a
    @34
    @1
    @26
    @27
    3anass
    cB
    @10
    c.x
    cG
    cM
    @8
    @9
    mulgmhm.b
    mulgmhm.m
    @10
    eqid
    #
    mulgnn0di
    sylan2br
    anassrs
    @29
    @11
    cB
    wcel
    #
    @12
    @30
    wceq
    @2
    @3
    @28
    @36
    @22
    @3
    @26
    @27
    @36
    cB
    @10
    cG
    @8
    @9
    mulgmhm.b
    @35
    mndcl
    3expb
    sylan
    vx
    @11
    @5
    @30
    cB
    @6
    @4
    @11
    cM
    c.x
    oveq2
    @25
    cM
    @11
    c.x
    ovex
    fvmpt
    syl
    @28
    @15
    @33
    wceq
    @2
    @26
    @27
    @13
    @31
    @14
    @32
    @10
    vx
    @8
    @5
    @31
    cB
    @6
    @4
    @8
    cM
    c.x
    oveq2
    @25
    cM
    @8
    c.x
    ovex
    fvmpt
    vx
    @9
    @5
    @32
    cB
    @6
    @4
    @9
    cM
    c.x
    oveq2
    @25
    cM
    @9
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @2
    @19
    cM
    @18
    c.x
    co
    #
    @18
    @2
    @3
    @18
    cB
    wcel
    @19
    @37
    wceq
    @22
    cB
    cG
    @18
    mulgmhm.b
    @18
    eqid
    #
    mndidcl
    vx
    @18
    @5
    @37
    cB
    @6
    @4
    @18
    cM
    c.x
    oveq2
    @25
    cM
    @18
    c.x
    ovex
    fvmpt
    3syl
    @0
    @3
    @1
    @37
    @18
    wceq
    @21
    cB
    c.x
    cG
    cM
    @18
    mulgmhm.b
    mulgmhm.m
    @38
    mulgnn0z
    sylan
    eqtrd
    3jca
    vy
    vz
    cB
    cB
    @10
    @10
    cG
    cG
    @6
    @18
    @18
    mulgmhm.b
    mulgmhm.b
    @35
    @35
    @38
    @38
    ismhm
    sylanbrc
end
