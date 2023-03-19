include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wf.mm"
include "cn0.mm"
include "cprime.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "ffvelrnd.mm"
include "wral.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "1arithlem2.mm"
include "sylan.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2.mm"
include "pcmpt.mm"
include "nnred.mm"
include "cr.mm"
include "prmz.mm"
include "zred.mm"
include "adantl.mm"
include "ifid.mm"
include "anassrs.mm"
include "ifeq2d.mm"
include "syl5reqr.mm"
include "iftrue.mm"
include "lecasei.mm"
include "3eqtrrd.mm"
include "wb.mm"
include "1arithlem3.mm"
include "syl.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqeq2d.mm"
include "rspcev.mm"

theorem 1arithlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vz: setvar z
  let cP: class P
  let cR: class R
  assume 1arith.1: |- M = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )
  assume 1arithlem4.2: |- G = ( y e. NN |-> if ( y e. Prime , ( y ^ ( F ` y ) ) , 1 ) )
  assume 1arithlem4.3: |- ( ph -> F : Prime --> NN0 )
  assume 1arithlem4.4: |- ( ph -> N e. NN )
  assume 1arithlem4.5: |- ( ( ph /\ ( q e. Prime /\ N <_ q ) ) -> ( F ` q ) = 0 )

  disjoint n p
  disjoint n q
  disjoint n x
  disjoint n y
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint x y
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint ph q
  disjoint ph y
  disjoint G n
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint e f
  disjoint e g
  disjoint e k
  disjoint e n
  disjoint e p
  disjoint e q
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n z
  disjoint p z
  disjoint q z
  disjoint x z
  disjoint y z
  disjoint M e
  disjoint M f
  disjoint M g
  disjoint P p
  disjoint R f
  disjoint R g
  disjoint R n
  disjoint R q
  disjoint R x
  disjoint R y
  assert |- ( ph -> E. x e. NN F = ( M ` x ) )

  proof
    wph
    cN
    cmul
    cG
    c1
    cseq
    #
    cfv
    #
    cn
    wcel
    #
    cF
    @1
    cM
    cfv
    #
    wceq
    #
    cF
    vx
    cv
    #
    cM
    cfv
    #
    wceq
    #
    vx
    cn
    wrex
    wph
    cn
    cn
    cN
    @0
    wph
    cn
    cn
    cG
    wf
    cn
    cn
    @0
    wf
    wph
    vy
    cv
    #
    cF
    cfv
    #
    vy
    cG
    1arithlem4.2
    wph
    @9
    cn0
    wcel
    #
    vy
    cprime
    wph
    cprime
    cn0
    @8
    cF
    1arithlem4.3
    ffvelrnda
    ralrimiva
    #
    pcmptcl
    simprd
    1arithlem4.4
    ffvelrnd
    #
    wph
    @4
    vq
    cv
    #
    cF
    cfv
    #
    @13
    @3
    cfv
    #
    wceq
    #
    vq
    cprime
    wral
    #
    wph
    @16
    vq
    cprime
    wph
    @13
    cprime
    wcel
    #
    wa
    #
    @15
    @13
    @1
    cpc
    co
    #
    @13
    cN
    cle
    wbr
    #
    @14
    cc0
    cif
    #
    @14
    wph
    @2
    @18
    @15
    @20
    wceq
    @12
    @13
    vn
    cM
    @1
    vp
    1arith.1
    1arithlem2
    sylan
    @19
    @9
    @14
    @13
    vy
    cG
    cN
    1arithlem4.2
    wph
    @10
    vy
    cprime
    wral
    @18
    @11
    adantr
    wph
    cN
    cn
    wcel
    @18
    1arithlem4.4
    adantr
    #
    wph
    @18
    simpr
    @8
    @13
    cF
    fveq2
    pcmpt
    @19
    @22
    @14
    wceq
    #
    cN
    @13
    @19
    cN
    @23
    nnred
    @18
    @13
    cr
    wcel
    wph
    @18
    @13
    @13
    prmz
    zred
    adantl
    @19
    cN
    @13
    cle
    wbr
    #
    wa
    #
    @14
    @21
    @14
    @14
    cif
    @22
    @21
    @14
    ifid
    @26
    @21
    @14
    cc0
    @14
    wph
    @18
    @25
    @14
    cc0
    wceq
    1arithlem4.5
    anassrs
    ifeq2d
    syl5reqr
    @21
    @24
    @19
    @21
    @14
    cc0
    iftrue
    adantl
    lecasei
    3eqtrrd
    ralrimiva
    wph
    cprime
    cn0
    cF
    wf
    #
    cprime
    cn0
    @3
    wf
    #
    @4
    @17
    wb
    #
    1arithlem4.3
    wph
    @2
    @28
    @12
    vn
    cM
    @1
    vp
    1arith.1
    1arithlem3
    syl
    @27
    cF
    cprime
    wfn
    @3
    cprime
    wfn
    @29
    @28
    cprime
    cn0
    cF
    ffn
    cprime
    cn0
    @3
    ffn
    vq
    cprime
    cF
    @3
    eqfnfv
    syl2an
    syl2anc
    mpbird
    @7
    @4
    vx
    @1
    cn
    @5
    @1
    wceq
    @6
    @3
    cF
    @5
    @1
    cM
    fveq2
    eqeq2d
    rspcev
    syl2anc
end
