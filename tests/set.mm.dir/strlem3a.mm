include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cch.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cort.mm"
include "wss.mm"
include "chj.mm"
include "caddc.mm"
include "wi.mm"
include "wral.mm"
include "cst.mm"
include "cpjh.mm"
include "c2.mm"
include "cexp.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "id.mm"
include "simpl.mm"
include "pjhcl.mm"
include "syl2anr.mm"
include "normcl.mm"
include "syl.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "normge0.mm"
include "pjnorm.mm"
include "simplr.mm"
include "breqtrd.mm"
include "w3a.mm"
include "cn0.mm"
include "2nn0.mm"
include "exple1.mm"
include "mpan2.mm"
include "syl3anc.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "fmptd.mm"
include "helch.mm"
include "strlem2.mm"
include "ax-mp.mm"
include "pjch1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "syl5eq.mm"
include "cva.mm"
include "pjcjt2.mm"
include "imp.mm"
include "pjopyth.mm"
include "eqtrd.mm"
include "chjcl.mm"
include "3adant3.mm"
include "adantr.mm"
include "3simpa.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "3exp1.mm"
include "com3r.mm"
include "ralrimdv.mm"
include "ralrimiv.mm"
include "isst.mm"

theorem strlem3a
  let vx: setvar x
  let vu: setvar u
  let cS: class S
  let vz: setvar z
  let vw: setvar w
  assume strlem3a.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )

  disjoint u x
  disjoint x z
  disjoint w x
  disjoint w z
  disjoint u z
  disjoint u w
  disjoint S z
  disjoint S w
  assert |- ( ( u e. ~H /\ ( normh ` u ) = 1 ) -> S e. States )

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
    cc0
    c1
    cicc
    co
    #
    cS
    wf
    chil
    cS
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
    @8
    chj
    co
    #
    cS
    cfv
    #
    @7
    cS
    cfv
    #
    @8
    cS
    cfv
    #
    caddc
    co
    #
    wceq
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
    cst
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
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @5
    cS
    @4
    @18
    cch
    wcel
    #
    wa
    #
    @21
    cr
    wcel
    cc0
    @21
    cle
    wbr
    @21
    c1
    cle
    wbr
    #
    @21
    @5
    wcel
    @23
    @20
    @23
    @19
    chil
    wcel
    #
    @20
    cr
    wcel
    #
    @22
    @22
    @1
    @25
    @4
    @22
    id
    #
    @1
    @3
    simpl
    #
    @0
    @18
    pjhcl
    syl2anr
    #
    @19
    normcl
    syl
    #
    resqcld
    @23
    @20
    @30
    sqge0d
    @23
    @26
    cc0
    @20
    cle
    wbr
    #
    @20
    c1
    cle
    wbr
    #
    @24
    @30
    @23
    @25
    @31
    @29
    @19
    normge0
    syl
    @23
    @20
    @2
    c1
    cle
    @22
    @22
    @1
    @20
    @2
    cle
    wbr
    @4
    @27
    @28
    @0
    @18
    pjnorm
    syl2anr
    @1
    @3
    @22
    simplr
    breqtrd
    @26
    @31
    @32
    w3a
    c2
    cn0
    wcel
    @24
    2nn0
    @20
    c2
    exple1
    mpan2
    syl3anc
    cc0
    c1
    @21
    0re
    1re
    elicc2i
    syl3anbrc
    strlem3a.1
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
    c2
    cexp
    co
    #
    c1
    chil
    cch
    wcel
    @6
    @35
    wceq
    helch
    vx
    vu
    chil
    cS
    strlem3a.1
    strlem2
    ax-mp
    @1
    @3
    @35
    @2
    c2
    cexp
    co
    #
    c1
    @1
    @34
    @2
    c2
    cexp
    @1
    @33
    @0
    cno
    @0
    pjch1
    fveq2d
    oveq1d
    @3
    @36
    c1
    c2
    cexp
    co
    c1
    @2
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    sylan9eq
    syl5eq
    @4
    @17
    vz
    cch
    @4
    @7
    cch
    wcel
    #
    @16
    vw
    cch
    @1
    @37
    @8
    cch
    wcel
    #
    @16
    wi
    wi
    @3
    @37
    @38
    @1
    @16
    @37
    @38
    @1
    @9
    @15
    @37
    @38
    @1
    w3a
    #
    @9
    wa
    #
    @0
    @10
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @0
    @7
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    c2
    cexp
    co
    #
    @0
    @8
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    @11
    @14
    @40
    @43
    @44
    @46
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @48
    @40
    @42
    @50
    c2
    cexp
    @40
    @41
    @49
    cno
    @39
    @9
    @41
    @49
    wceq
    @0
    @8
    @7
    pjcjt2
    imp
    fveq2d
    oveq1d
    @39
    @9
    @51
    @48
    wceq
    @0
    @8
    @7
    pjopyth
    imp
    eqtrd
    @40
    @10
    cch
    wcel
    #
    @11
    @43
    wceq
    @39
    @52
    @9
    @37
    @38
    @52
    @1
    @7
    @8
    chjcl
    3adant3
    adantr
    vx
    vu
    @10
    cS
    strlem3a.1
    strlem2
    syl
    @40
    @37
    @38
    wa
    #
    @14
    @48
    wceq
    @39
    @53
    @9
    @37
    @38
    @1
    3simpa
    adantr
    @37
    @38
    @12
    @45
    @13
    @47
    caddc
    vx
    vu
    @7
    cS
    strlem3a.1
    strlem2
    vx
    vu
    @8
    cS
    strlem3a.1
    strlem2
    oveqan12d
    syl
    3eqtr4d
    3exp1
    com3r
    adantr
    ralrimdv
    ralrimiv
    vz
    vw
    cS
    isst
    syl3anbrc
end
