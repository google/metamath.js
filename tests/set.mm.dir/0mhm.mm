include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "id.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantl.mm"
include "fconst6g.mm"
include "syl.mm"
include "simpr.mm"
include "mndlid.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mndcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem 0mhm
  let cB: class B
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume 0mhm.z: |- .0. = ( 0g ` N )
  assume 0mhm.b: |- B = ( Base ` M )


  assert |- ( ( M e. Mnd /\ N e. Mnd ) -> ( B X. { .0. } ) e. ( M MndHom N ) )

  proof
    cM
    cmnd
    wcel
    #
    cN
    cmnd
    wcel
    #
    wa
    #
    @2
    cB
    cN
    cbs
    cfv
    #
    cB
    c.0
    csn
    cxp
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @4
    cfv
    #
    @6
    @4
    cfv
    #
    @7
    @4
    cfv
    #
    cN
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cM
    c0g
    cfv
    #
    @4
    cfv
    c.0
    wceq
    #
    w3a
    @4
    cM
    cN
    cmhm
    co
    wcel
    @2
    id
    @2
    @5
    @16
    @18
    @2
    c.0
    @3
    wcel
    #
    @5
    @1
    @19
    @0
    @3
    cN
    c.0
    @3
    eqid
    #
    0mhm.z
    mndidcl
    adantl
    #
    cB
    c.0
    @3
    fconst6g
    syl
    @2
    @15
    vx
    vy
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
    c.0
    @13
    co
    #
    @10
    @14
    @2
    c.0
    @26
    wceq
    #
    @24
    @2
    @1
    @19
    @27
    @0
    @1
    simpr
    @21
    @1
    @19
    wa
    @26
    c.0
    @3
    @13
    cN
    c.0
    c.0
    @20
    @13
    eqid
    #
    0mhm.z
    mndlid
    eqcomd
    syl2anc
    adantr
    @25
    @9
    cB
    wcel
    #
    @10
    c.0
    wceq
    @0
    @24
    @29
    @1
    @0
    @22
    @23
    @29
    cB
    @8
    cM
    @6
    @7
    0mhm.b
    @8
    eqid
    #
    mndcl
    3expb
    adantlr
    cB
    c.0
    @9
    c.0
    cN
    c0g
    cfv
    cvv
    0mhm.z
    cN
    c0g
    fvex
    eqeltri
    #
    fvconst2
    syl
    @24
    @14
    @26
    wceq
    @2
    @22
    @23
    @11
    c.0
    @12
    c.0
    @13
    cB
    c.0
    @6
    @31
    fvconst2
    cB
    c.0
    @7
    @31
    fvconst2
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @2
    @17
    cB
    wcel
    #
    @18
    @0
    @32
    @1
    cB
    cM
    @17
    0mhm.b
    @17
    eqid
    #
    mndidcl
    adantr
    cB
    c.0
    @17
    @31
    fvconst2
    syl
    3jca
    vx
    vy
    cB
    @3
    @8
    @13
    cM
    cN
    @4
    c.0
    @17
    0mhm.b
    @20
    @30
    @28
    @33
    0mhm.z
    ismhm
    sylanbrc
end
