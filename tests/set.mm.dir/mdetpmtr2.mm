include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "ctpos.mm"
include "cfv.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "mattposcl.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "cv.mm"
include "cmpt2.mm"
include "ovtpos.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "tposmpt2.mm"
include "mdetpmtr1.mm"
include "syl22anc.mm"
include "mdettpos.mm"
include "ad2ant2r.mm"
include "cbs.mm"
include "eqid.mm"
include "w3a.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "csymg.mm"
include "symgfv.mm"
include "syl2anc.mm"
include "simp1rl.mm"
include "matecld.mm"
include "matbas2d.mm"
include "syl5eqel.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem mdetpmtr2
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vk: setvar k
  let vl: setvar l
  assume mdetpmtr.a: |- A = ( N Mat R )
  assume mdetpmtr.b: |- B = ( Base ` A )
  assume mdetpmtr.d: |- D = ( N maDet R )
  assume mdetpmtr.g: |- G = ( Base ` ( SymGrp ` N ) )
  assume mdetpmtr.s: |- S = ( pmSgn ` N )
  assume mdetpmtr.z: |- Z = ( ZRHom ` R )
  assume mdetpmtr.t: |- .x. = ( .r ` R )
  assume mdetpmtr2.e: |- E = ( i e. N , j e. N |-> ( i M ( P ` j ) ) )

  disjoint B i
  disjoint B j
  disjoint i j
  disjoint G i
  disjoint G j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint .x. p
  disjoint .x. q
  disjoint p q
  disjoint B p
  disjoint B x
  disjoint i p
  disjoint i x
  disjoint j p
  disjoint j x
  disjoint p x
  disjoint B q
  disjoint q x
  disjoint E p
  disjoint E x
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint i q
  disjoint j q
  disjoint M k
  disjoint M l
  disjoint M p
  disjoint M q
  disjoint M x
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint l p
  disjoint l q
  disjoint l x
  disjoint N k
  disjoint N l
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint P k
  disjoint P l
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint R k
  disjoint R l
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint S p
  disjoint S q
  disjoint Z p
  disjoint Z q
  assert |- ( ( ( R e. CRing /\ N e. Fin ) /\ ( M e. B /\ P e. G ) ) -> ( D ` M ) = ( ( ( Z o. S ) ` P ) .x. ( D ` E ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    cP
    cG
    wcel
    #
    wa
    #
    wa
    #
    cM
    ctpos
    #
    cD
    cfv
    #
    cP
    cZ
    cS
    ccom
    cfv
    #
    cE
    ctpos
    #
    cD
    cfv
    #
    c.x
    co
    #
    cM
    cD
    cfv
    #
    @9
    cE
    cD
    cfv
    #
    c.x
    co
    @6
    @0
    @1
    @7
    cB
    wcel
    #
    @4
    @8
    @12
    wceq
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    @3
    @15
    @2
    @4
    cA
    cB
    cR
    cM
    cN
    mdetpmtr.a
    mdetpmtr.b
    mattposcl
    ad2antrl
    @2
    @3
    @4
    simprr
    #
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    vj
    vi
    @10
    cG
    @7
    cN
    cZ
    mdetpmtr.a
    mdetpmtr.b
    mdetpmtr.d
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    mdetpmtr.t
    vi
    vj
    cN
    cN
    vj
    cv
    #
    cP
    cfv
    #
    vi
    cv
    #
    @7
    co
    #
    cE
    cE
    vi
    vj
    cN
    cN
    @21
    @20
    cM
    co
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @22
    cmpt2
    mdetpmtr2.e
    vi
    vj
    cN
    cN
    @23
    @22
    @23
    @22
    wceq
    @21
    cN
    wcel
    #
    @19
    cN
    wcel
    #
    wa
    @22
    @23
    @20
    @21
    cM
    ovtpos
    eqcomi
    a1i
    mpt2eq3ia
    eqtri
    tposmpt2
    mdetpmtr1
    syl22anc
    @0
    @3
    @8
    @13
    wceq
    @1
    @4
    cA
    cB
    cD
    cR
    cM
    cN
    mdetpmtr.d
    mdetpmtr.a
    mdetpmtr.b
    mdettpos
    ad2ant2r
    @6
    @11
    @14
    @9
    c.x
    @6
    @0
    cE
    cB
    wcel
    @11
    @14
    wceq
    @16
    @6
    cE
    @24
    cB
    mdetpmtr2.e
    @6
    vi
    vj
    cA
    cB
    @23
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    mdetpmtr.a
    @27
    eqid
    #
    mdetpmtr.b
    @17
    @16
    @6
    @25
    @26
    w3a
    #
    cA
    cB
    cR
    @21
    @20
    @27
    cM
    cN
    mdetpmtr.a
    @28
    mdetpmtr.b
    @6
    @25
    @26
    simp2
    @29
    @4
    @26
    @20
    cN
    wcel
    @6
    @25
    @4
    @26
    @18
    3ad2ant1
    @6
    @25
    @26
    simp3
    cN
    cG
    cP
    cN
    csymg
    cfv
    #
    @19
    @30
    eqid
    mdetpmtr.g
    symgfv
    syl2anc
    @3
    @4
    @2
    @25
    @26
    simp1rl
    matecld
    matbas2d
    syl5eqel
    cA
    cB
    cD
    cR
    cE
    cN
    mdetpmtr.d
    mdetpmtr.a
    mdetpmtr.b
    mdettpos
    syl2anc
    oveq2d
    3eqtr3d
end
