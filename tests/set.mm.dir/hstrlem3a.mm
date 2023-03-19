include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cch.mm"
include "wf.mm"
include "cort.mm"
include "wss.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "chj.mm"
include "cva.mm"
include "wi.mm"
include "wral.mm"
include "chst.mm"
include "cpjh.mm"
include "pjhcl.mm"
include "ancoms.mm"
include "adantlr.mm"
include "fmptd.mm"
include "helch.mm"
include "hstrlem2.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "pjch1.mm"
include "fveq2d.mm"
include "id.mm"
include "sylan9eq.mm"
include "syl5eq.mm"
include "w3a.mm"
include "oveqan12d.mm"
include "3adant3.mm"
include "adantr.mm"
include "pjoi0.mm"
include "eqtrd.mm"
include "pjcjt2.mm"
include "imp.mm"
include "chjcl.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "jca.mm"
include "3exp1.mm"
include "com3r.mm"
include "ralrimdv.mm"
include "ralrimiv.mm"
include "ishst.mm"
include "syl3anbrc.mm"

theorem hstrlem3a
  let vx: setvar x
  let vu: setvar u
  let cS: class S
  let vz: setvar z
  let vw: setvar w
  assume hstrlem3a.1: |- S = ( x e. CH |-> ( ( projh ` x ) ` u ) )

  disjoint u x
  disjoint x z
  disjoint w x
  disjoint w z
  disjoint u z
  disjoint u w
  disjoint S z
  disjoint S w
  assert |- ( ( u e. ~H /\ ( normh ` u ) = 1 ) -> S e. CHStates )

  proof
    vu
    cv
    #
    chil
    wcel
    #
    @0
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cch
    chil
    cS
    wf
    chil
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    vz
    cv
    #
    vw
    cv
    #
    cort
    cfv
    wss
    #
    @7
    cS
    cfv
    #
    @8
    cS
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    @7
    @8
    chj
    co
    #
    cS
    cfv
    #
    @10
    @11
    cva
    co
    #
    wceq
    #
    wa
    #
    wi
    #
    vw
    cch
    wral
    #
    vz
    cch
    wral
    cS
    chst
    wcel
    @4
    vx
    cch
    @0
    vx
    cv
    #
    cpjh
    cfv
    cfv
    #
    chil
    cS
    @1
    @21
    cch
    wcel
    #
    @22
    chil
    wcel
    #
    @3
    @23
    @1
    @24
    @0
    @21
    pjhcl
    ancoms
    adantlr
    hstrlem3a.1
    fmptd
    @4
    @6
    @0
    chil
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c1
    @5
    @25
    cno
    chil
    cch
    wcel
    @5
    @25
    wceq
    helch
    vx
    vu
    chil
    cS
    hstrlem3a.1
    hstrlem2
    ax-mp
    fveq2i
    @1
    @3
    @26
    @2
    c1
    @1
    @25
    @0
    cno
    @0
    pjch1
    fveq2d
    @3
    id
    sylan9eq
    syl5eq
    @4
    @20
    vz
    cch
    @4
    @7
    cch
    wcel
    #
    @19
    vw
    cch
    @1
    @27
    @8
    cch
    wcel
    #
    @19
    wi
    wi
    @3
    @27
    @28
    @1
    @19
    @27
    @28
    @1
    @9
    @18
    @27
    @28
    @1
    w3a
    #
    @9
    wa
    #
    @13
    @17
    @30
    @12
    @0
    @7
    cpjh
    cfv
    cfv
    #
    @0
    @8
    cpjh
    cfv
    cfv
    #
    csp
    co
    #
    cc0
    @29
    @12
    @33
    wceq
    #
    @9
    @27
    @28
    @34
    @1
    @27
    @28
    @10
    @31
    @11
    @32
    csp
    vx
    vu
    @7
    cS
    hstrlem3a.1
    hstrlem2
    #
    vx
    vu
    @8
    cS
    hstrlem3a.1
    hstrlem2
    #
    oveqan12d
    3adant3
    adantr
    @0
    @7
    @8
    pjoi0
    eqtrd
    @30
    @0
    @14
    cpjh
    cfv
    cfv
    #
    @31
    @32
    cva
    co
    #
    @15
    @16
    @29
    @9
    @37
    @38
    wceq
    @0
    @8
    @7
    pjcjt2
    imp
    @29
    @15
    @37
    wceq
    #
    @9
    @27
    @28
    @39
    @1
    @27
    @28
    wa
    @14
    cch
    wcel
    @39
    @7
    @8
    chjcl
    vx
    vu
    @14
    cS
    hstrlem3a.1
    hstrlem2
    syl
    3adant3
    adantr
    @29
    @16
    @38
    wceq
    #
    @9
    @27
    @28
    @40
    @1
    @27
    @28
    @10
    @31
    @11
    @32
    cva
    @35
    @36
    oveqan12d
    3adant3
    adantr
    3eqtr4d
    jca
    3exp1
    com3r
    adantr
    ralrimdv
    ralrimiv
    vz
    vw
    cS
    ishst
    syl3anbrc
end
