include "cho.mm"
include "wcel.mm"
include "cei.mm"
include "cfv.mm"
include "wa.mm"
include "cel.mm"
include "wne.mm"
include "chil.mm"
include "cc.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "ccj.mm"
include "csp.mm"
include "cc0.mm"
include "wf.mm"
include "hmopf.mm"
include "eleigveccl.mm"
include "sylan.mm"
include "adantr.mm"
include "adantlr.mm"
include "jca.mm"
include "eighmre.mm"
include "recnd.mm"
include "adantrr.mm"
include "c0v.mm"
include "eigvec1.mm"
include "simpld.mm"
include "cjred.mm"
include "neeq2d.mm"
include "biimpar.mm"
include "anasss.mm"
include "simpll.mm"
include "hmop.mm"
include "syl3anc.mm"
include "eigorth.mm"
include "biimpa.mm"
include "syl21anc.mm"

theorem eighmorth
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( ( T e. HrmOp /\ A e. ( eigvec ` T ) ) /\ ( B e. ( eigvec ` T ) /\ ( ( eigval ` T ) ` A ) =/= ( ( eigval ` T ) ` B ) ) ) -> ( A .ih B ) = 0 )

  proof
    cT
    cho
    wcel
    #
    cA
    cT
    cei
    cfv
    #
    wcel
    #
    wa
    #
    cB
    @1
    wcel
    #
    cA
    cT
    cel
    cfv
    #
    cfv
    #
    cB
    @5
    cfv
    #
    wne
    #
    wa
    #
    wa
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    wa
    #
    wa
    #
    cA
    cT
    cfv
    #
    @6
    cA
    csm
    co
    wceq
    #
    cB
    cT
    cfv
    #
    @7
    cB
    csm
    co
    wceq
    #
    wa
    #
    @6
    @7
    ccj
    cfv
    #
    wne
    #
    wa
    #
    cA
    @20
    csp
    co
    @18
    cB
    csp
    co
    wceq
    #
    cA
    cB
    csp
    co
    cc0
    wceq
    #
    @3
    @4
    @17
    @8
    @3
    @4
    wa
    #
    @13
    @16
    @28
    @11
    @12
    @3
    @11
    @4
    @0
    chil
    chil
    cT
    wf
    #
    @2
    @11
    cT
    hmopf
    #
    cA
    cT
    eleigveccl
    sylan
    adantr
    #
    @0
    @4
    @12
    @2
    @0
    @29
    @4
    @12
    @30
    cB
    cT
    eleigveccl
    sylan
    adantlr
    #
    jca
    @28
    @14
    @15
    @3
    @14
    @4
    @3
    @6
    cA
    cT
    eighmre
    recnd
    adantr
    @0
    @4
    @15
    @2
    @0
    @4
    wa
    #
    @7
    cB
    cT
    eighmre
    #
    recnd
    adantlr
    jca
    jca
    adantrr
    @10
    @22
    @24
    @3
    @4
    @22
    @8
    @28
    @19
    @21
    @3
    @19
    @4
    @0
    @29
    @2
    @19
    @30
    @29
    @2
    wa
    @19
    cA
    c0v
    wne
    cA
    cT
    eigvec1
    simpld
    sylan
    adantr
    @0
    @4
    @21
    @2
    @0
    @29
    @4
    @21
    @30
    @29
    @4
    wa
    @21
    cB
    c0v
    wne
    cB
    cT
    eigvec1
    simpld
    sylan
    adantlr
    jca
    adantrr
    @0
    @9
    @24
    @2
    @0
    @4
    @8
    @24
    @33
    @24
    @8
    @33
    @23
    @7
    @6
    @33
    @7
    @34
    cjred
    neeq2d
    biimpar
    anasss
    adantlr
    jca
    @3
    @4
    @26
    @8
    @28
    @0
    @11
    @12
    @26
    @0
    @2
    @4
    simpll
    @31
    @32
    cA
    cB
    cT
    hmop
    syl3anc
    adantrr
    @17
    @25
    wa
    @26
    @27
    cA
    cB
    @6
    @7
    cT
    eigorth
    biimpa
    syl21anc
end
