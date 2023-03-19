include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "ctpos.mm"
include "wceq.mm"
include "simpr.mm"
include "maduf.mm"
include "ffvelrnda.mm"
include "ancoms.mm"
include "simpl.mm"
include "mattposm.mm"
include "syl3anc.mm"
include "madutpos.mm"
include "oveq2d.mm"
include "mattposcl.mm"
include "madurid.mm"
include "sylan.mm"
include "3eqtr2d.mm"
include "tposeqd.mm"
include "crg.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "crngring.mm"
include "matring.mm"
include "syl2an.mm"
include "ringcl.mm"
include "mattpostpos.mm"
include "syl.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "mdetf.mm"
include "adantl.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "ringidcl.mm"
include "mattposvs.mm"
include "syl2anc.mm"
include "mdettpos.mm"
include "mattpos1.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem madulid
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.1: class .1.
  let cJ: class J
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume madurid.a: |- A = ( N Mat R )
  assume madurid.b: |- B = ( Base ` A )
  assume madurid.j: |- J = ( N maAdju R )
  assume madurid.d: |- D = ( N maDet R )
  assume madurid.i: |- .1. = ( 1r ` A )
  assume madurid.t: |- .x. = ( .r ` A )
  assume madurid.s: |- .xb = ( .s ` A )


  assert |- ( ( M e. B /\ R e. CRing ) -> ( ( J ` M ) .x. M ) = ( ( D ` M ) .xb .1. ) )

  proof
    cM
    cB
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cJ
    cfv
    #
    cM
    c.x
    co
    #
    ctpos
    #
    ctpos
    #
    cM
    ctpos
    #
    cD
    cfv
    #
    c.1
    c.xb
    co
    #
    ctpos
    #
    @4
    cM
    cD
    cfv
    #
    c.1
    c.xb
    co
    #
    @2
    @5
    @9
    @2
    @5
    @7
    @3
    ctpos
    #
    c.x
    co
    #
    @7
    @7
    cJ
    cfv
    #
    c.x
    co
    #
    @9
    @2
    @1
    @3
    cB
    wcel
    #
    @0
    @5
    @14
    wceq
    @0
    @1
    simpr
    @1
    @0
    @17
    @1
    cB
    cB
    cM
    cJ
    cA
    cB
    cR
    cJ
    cN
    madurid.a
    madurid.j
    madurid.b
    maduf
    ffvelrnda
    ancoms
    #
    @0
    @1
    simpl
    #
    cA
    cB
    cR
    c.x
    cN
    @3
    cM
    madurid.a
    madurid.b
    madurid.t
    mattposm
    syl3anc
    @2
    @15
    @13
    @7
    c.x
    @1
    @0
    @15
    @13
    wceq
    cA
    cB
    cR
    cJ
    cM
    cN
    madurid.a
    madurid.j
    madurid.b
    madutpos
    ancoms
    oveq2d
    @0
    @7
    cB
    wcel
    #
    @1
    @16
    @9
    wceq
    cA
    cB
    cR
    cM
    cN
    madurid.a
    madurid.b
    mattposcl
    #
    cA
    cB
    cD
    cR
    c.xb
    c.x
    c.1
    cJ
    @7
    cN
    madurid.a
    madurid.b
    madurid.j
    madurid.d
    madurid.i
    madurid.t
    madurid.s
    madurid
    sylan
    3eqtr2d
    tposeqd
    @2
    @4
    cB
    wcel
    #
    @6
    @4
    wceq
    @2
    cA
    crg
    wcel
    #
    @17
    @0
    @22
    @0
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    @23
    @1
    @0
    @24
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madurid.a
    madurid.b
    matrcl
    simpld
    #
    cR
    crngring
    #
    cA
    cR
    cN
    madurid.a
    matring
    syl2an
    #
    @18
    @19
    cB
    cA
    c.x
    @3
    cM
    madurid.b
    madurid.t
    ringcl
    syl3anc
    cA
    cB
    cR
    @4
    cN
    madurid.a
    madurid.b
    mattpostpos
    syl
    @2
    @10
    @8
    c.1
    ctpos
    #
    c.xb
    co
    #
    @12
    @2
    @8
    cR
    cbs
    cfv
    #
    wcel
    c.1
    cB
    wcel
    #
    @10
    @30
    wceq
    @2
    cB
    @31
    @7
    cD
    @1
    cB
    @31
    cD
    wf
    @0
    cA
    cB
    cD
    cR
    @31
    cN
    madurid.d
    madurid.a
    madurid.b
    @31
    eqid
    #
    mdetf
    adantl
    @0
    @20
    @1
    @21
    adantr
    ffvelrnd
    @2
    @23
    @32
    @28
    cB
    cA
    c.1
    madurid.b
    madurid.i
    ringidcl
    syl
    cA
    cB
    cR
    c.xb
    @31
    cN
    @8
    c.1
    madurid.a
    madurid.b
    @33
    madurid.s
    mattposvs
    syl2anc
    @2
    @8
    @11
    @29
    c.1
    c.xb
    @1
    @0
    @8
    @11
    wceq
    cA
    cB
    cD
    cR
    cM
    cN
    madurid.d
    madurid.a
    madurid.b
    mdettpos
    ancoms
    @0
    @24
    @25
    @29
    c.1
    wceq
    @1
    @26
    @27
    cA
    cR
    c.1
    cN
    madurid.a
    madurid.i
    mattpos1
    syl2an
    oveq12d
    eqtrd
    3eqtr3d
end
