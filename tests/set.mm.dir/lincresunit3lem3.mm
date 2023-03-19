include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cur.mm"
include "3simpa.mm"
include "adantr.mm"
include "eqid.mm"
include "lmodvs1.mm"
include "syl.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "unitnegcl.mm"
include "sylan.mm"
include "3ad2antl1.mm"
include "jca.mm"
include "unitlinv.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "simpl1.mm"
include "ringinvcl.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "unitcl.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "simpl2.mm"
include "3jca.mm"
include "lmodvsass.mm"
include "oveq2.mm"
include "adantl.mm"
include "simpl3.mm"
include "3eqtrd.mm"
include "3simpb.mm"
include "ex.mm"
include "impbid1.mm"

theorem lincresunit3lem3
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume lincresunit3lem3.b: |- B = ( Base ` M )
  assume lincresunit3lem3.r: |- R = ( Scalar ` M )
  assume lincresunit3lem3.e: |- E = ( Base ` R )
  assume lincresunit3lem3.u: |- U = ( Unit ` R )
  assume lincresunit3lem3.n: |- N = ( invg ` R )
  assume lincresunit3lem3.t: |- .x. = ( .s ` M )


  assert |- ( ( ( M e. LMod /\ X e. B /\ Y e. B ) /\ A e. U ) -> ( ( ( N ` A ) .x. X ) = ( ( N ` A ) .x. Y ) <-> X = Y ) )

  proof
    cM
    clmod
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cA
    cU
    wcel
    #
    wa
    #
    cA
    cN
    cfv
    #
    cX
    c.x
    co
    #
    @6
    cY
    c.x
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    @5
    @9
    @10
    @5
    @9
    wa
    #
    cX
    @6
    cR
    cinvr
    cfv
    #
    cfv
    #
    @6
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cY
    c.x
    co
    #
    cY
    @5
    cX
    @16
    wceq
    @9
    @5
    @17
    cX
    c.x
    co
    #
    cX
    @16
    @5
    @0
    @1
    wa
    #
    @19
    cX
    wceq
    @3
    @20
    @4
    @0
    @1
    @2
    3simpa
    adantr
    c.x
    @17
    cR
    cB
    cM
    cX
    lincresunit3lem3.b
    lincresunit3lem3.r
    lincresunit3lem3.t
    @17
    eqid
    #
    lmodvs1
    syl
    @5
    @17
    @15
    cX
    c.x
    @5
    @15
    @17
    @5
    cR
    crg
    wcel
    #
    @6
    cU
    wcel
    #
    wa
    #
    @15
    @17
    wceq
    #
    @5
    @22
    @23
    @3
    @22
    @4
    @0
    @1
    @22
    @2
    cR
    cM
    lincresunit3lem3.r
    lmodring
    #
    3ad2ant1
    adantr
    @0
    @1
    @4
    @23
    @2
    @0
    @22
    @4
    @23
    @26
    cR
    cU
    cN
    cA
    lincresunit3lem3.u
    lincresunit3lem3.n
    unitnegcl
    sylan
    3ad2antl1
    jca
    #
    cR
    @14
    cU
    @17
    @12
    @6
    lincresunit3lem3.u
    @12
    eqid
    #
    @14
    eqid
    #
    @21
    unitlinv
    #
    syl
    eqcomd
    oveq1d
    eqtr3d
    adantr
    @11
    @16
    @13
    @7
    c.x
    co
    #
    @13
    @8
    c.x
    co
    #
    @18
    @11
    @0
    @13
    cE
    wcel
    #
    @6
    cE
    wcel
    #
    @1
    w3a
    #
    wa
    #
    @16
    @31
    wceq
    @5
    @36
    @9
    @5
    @0
    @35
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @33
    @34
    @1
    @5
    @24
    @33
    @27
    cE
    cR
    cU
    @12
    @6
    lincresunit3lem3.u
    @28
    lincresunit3lem3.e
    ringinvcl
    syl
    #
    @3
    cR
    cgrp
    wcel
    #
    cA
    cE
    wcel
    @34
    @4
    @0
    @1
    @39
    @2
    cR
    cM
    lincresunit3lem3.r
    lmodfgrp
    3ad2ant1
    cE
    cR
    cU
    cA
    lincresunit3lem3.e
    lincresunit3lem3.u
    unitcl
    cE
    cR
    cN
    cA
    lincresunit3lem3.e
    lincresunit3lem3.n
    grpinvcl
    syl2an
    #
    @0
    @1
    @2
    @4
    simpl2
    3jca
    jca
    adantr
    @13
    @6
    c.x
    @14
    cR
    cE
    cB
    cM
    cX
    lincresunit3lem3.b
    lincresunit3lem3.r
    lincresunit3lem3.t
    lincresunit3lem3.e
    @29
    lmodvsass
    syl
    @9
    @31
    @32
    wceq
    @5
    @7
    @8
    @13
    c.x
    oveq2
    adantl
    @11
    @15
    cY
    c.x
    co
    #
    @32
    @18
    @11
    @0
    @33
    @34
    @2
    w3a
    #
    wa
    @41
    @32
    wceq
    @11
    @0
    @42
    @5
    @0
    @9
    @37
    adantr
    @5
    @42
    @9
    @5
    @33
    @34
    @2
    @38
    @40
    @0
    @1
    @2
    @4
    simpl3
    3jca
    adantr
    jca
    @13
    @6
    c.x
    @14
    cR
    cE
    cB
    cM
    cY
    lincresunit3lem3.b
    lincresunit3lem3.r
    lincresunit3lem3.t
    lincresunit3lem3.e
    @29
    lmodvsass
    syl
    @11
    @15
    @17
    cY
    c.x
    @11
    @24
    @25
    @5
    @24
    @9
    @27
    adantr
    @30
    syl
    oveq1d
    eqtr3d
    3eqtrd
    @11
    @0
    @2
    wa
    #
    @18
    cY
    wceq
    @5
    @43
    @9
    @3
    @43
    @4
    @0
    @1
    @2
    3simpb
    adantr
    adantr
    c.x
    @17
    cR
    cB
    cM
    cY
    lincresunit3lem3.b
    lincresunit3lem3.r
    lincresunit3lem3.t
    @21
    lmodvs1
    syl
    3eqtrd
    ex
    cX
    cY
    @6
    c.x
    oveq2
    impbid1
end
