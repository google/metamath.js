include "cva.mm"
include "co.mm"
include "csp.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cno.mm"
include "cle.mm"
include "c2.mm"
include "cexp.mm"
include "wbr.mm"
include "cmul.mm"
include "c1.mm"
include "ccj.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "1re.mm"
include "ax-1cn.mm"
include "cjrebi.mm"
include "mpbi.mm"
include "oveq1i.mm"
include "hicli.mm"
include "mulid2i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "abs1.mm"
include "normlem7.mm"
include "eqbrtrri.mm"
include "cneg.mm"
include "eqid.mm"
include "normlem2.mm"
include "cjcli.mm"
include "mulcli.mm"
include "addcli.mm"
include "negrebi.mm"
include "eqeltrri.mm"
include "2re.mm"
include "cc0.mm"
include "chil.mm"
include "hiidge0.mm"
include "ax-mp.mm"
include "hiidrcl.mm"
include "sqrtcli.mm"
include "remulcli.mm"
include "readdcli.mm"
include "leadd2i.mm"
include "normlem8.mm"
include "addcomi.mm"
include "oveq2i.mm"
include "recni.mm"
include "binom2i.mm"
include "sqcli.mm"
include "2cn.mm"
include "add32i.mm"
include "sqsqrti.mm"
include "3eqtri.mm"
include "3brtr4i.mm"
include "wb.mm"
include "hvaddcli.mm"
include "sqge0i.mm"
include "resqcli.mm"
include "sqrtlei.mm"
include "mp2an.mm"
include "sqrtge0i.mm"
include "addge0i.mm"
include "sqrtsqi.mm"
include "breqtri.mm"
include "normval.mm"

theorem norm-ii-i
  let cA: class A
  let cB: class B
  assume norm-ii.1: |- A e. ~H
  assume norm-ii.2: |- B e. ~H


  assert |- ( normh ` ( A +h B ) ) <_ ( ( normh ` A ) + ( normh ` B ) )

  proof
    cA
    cB
    cva
    co
    #
    @0
    csp
    co
    #
    csqrt
    cfv
    #
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    #
    cB
    cB
    csp
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @0
    cno
    cfv
    #
    cA
    cno
    cfv
    #
    cB
    cno
    cfv
    #
    caddc
    co
    cle
    @2
    @7
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @7
    cle
    @1
    @11
    cle
    wbr
    #
    @2
    @12
    cle
    wbr
    #
    @3
    @5
    caddc
    co
    #
    cB
    cA
    csp
    co
    #
    cA
    cB
    csp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @15
    c2
    @4
    @6
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    @11
    cle
    @18
    @21
    cle
    wbr
    @19
    @22
    cle
    wbr
    c1
    ccj
    cfv
    #
    @16
    cmul
    co
    #
    c1
    @17
    cmul
    co
    #
    caddc
    co
    #
    @18
    @21
    cle
    @24
    @16
    @25
    @17
    caddc
    @24
    c1
    @16
    cmul
    co
    @16
    @23
    c1
    @16
    cmul
    c1
    cr
    wcel
    @23
    c1
    wceq
    1re
    c1
    ax-1cn
    cjrebi
    mpbi
    oveq1i
    @16
    cB
    cA
    norm-ii.2
    norm-ii.1
    hicli
    #
    mulid2i
    eqtri
    @17
    cA
    cB
    norm-ii.1
    norm-ii.2
    hicli
    #
    mulid2i
    oveq12i
    #
    c1
    cB
    cA
    ax-1cn
    norm-ii.2
    norm-ii.1
    abs1
    normlem7
    eqbrtrri
    @18
    @21
    @15
    @26
    @18
    cr
    @29
    @26
    cneg
    #
    cr
    wcel
    @26
    cr
    wcel
    @30
    c1
    cB
    cA
    ax-1cn
    norm-ii.2
    norm-ii.1
    @30
    eqid
    normlem2
    @26
    @24
    @25
    @23
    @16
    c1
    ax-1cn
    cjcli
    @27
    mulcli
    c1
    @17
    ax-1cn
    @28
    mulcli
    addcli
    negrebi
    mpbi
    eqeltrri
    c2
    @20
    2re
    @4
    @6
    cc0
    @3
    cle
    wbr
    #
    @4
    cr
    wcel
    cA
    chil
    wcel
    #
    @31
    norm-ii.1
    cA
    hiidge0
    ax-mp
    #
    @3
    @32
    @3
    cr
    wcel
    norm-ii.1
    cA
    hiidrcl
    ax-mp
    #
    sqrtcli
    ax-mp
    #
    cc0
    @5
    cle
    wbr
    #
    @6
    cr
    wcel
    cB
    chil
    wcel
    #
    @36
    norm-ii.2
    cB
    hiidge0
    ax-mp
    #
    @5
    @37
    @5
    cr
    wcel
    norm-ii.2
    cB
    hiidrcl
    ax-mp
    #
    sqrtcli
    ax-mp
    #
    remulcli
    remulcli
    @3
    @5
    @34
    @39
    readdcli
    leadd2i
    mpbi
    @1
    @15
    @17
    @16
    caddc
    co
    #
    caddc
    co
    @19
    cA
    cB
    cA
    cB
    norm-ii.1
    norm-ii.2
    norm-ii.1
    norm-ii.2
    normlem8
    @41
    @18
    @15
    caddc
    @17
    @16
    @28
    @27
    addcomi
    oveq2i
    eqtri
    @11
    @4
    c2
    cexp
    co
    #
    @21
    caddc
    co
    @6
    c2
    cexp
    co
    #
    caddc
    co
    @42
    @43
    caddc
    co
    #
    @21
    caddc
    co
    @22
    @4
    @6
    @4
    @35
    recni
    #
    @6
    @40
    recni
    #
    binom2i
    @42
    @21
    @43
    @4
    @45
    sqcli
    c2
    @20
    2cn
    @4
    @6
    @45
    @46
    mulcli
    mulcli
    @6
    @46
    sqcli
    add32i
    @44
    @15
    @21
    caddc
    @42
    @3
    @43
    @5
    caddc
    @31
    @42
    @3
    wceq
    @33
    @3
    @34
    sqsqrti
    ax-mp
    @36
    @43
    @5
    wceq
    @38
    @5
    @39
    sqsqrti
    ax-mp
    oveq12i
    oveq1i
    3eqtri
    3brtr4i
    cc0
    @1
    cle
    wbr
    #
    cc0
    @11
    cle
    wbr
    @13
    @14
    wb
    @0
    chil
    wcel
    #
    @47
    cA
    cB
    norm-ii.1
    norm-ii.2
    hvaddcli
    #
    @0
    hiidge0
    ax-mp
    @7
    @4
    @6
    @35
    @40
    readdcli
    #
    sqge0i
    @1
    @11
    @48
    @1
    cr
    wcel
    @49
    @0
    hiidrcl
    ax-mp
    @7
    @50
    resqcli
    sqrtlei
    mp2an
    mpbi
    cc0
    @7
    cle
    wbr
    #
    @12
    @7
    wceq
    cc0
    @4
    cle
    wbr
    #
    cc0
    @6
    cle
    wbr
    #
    @51
    @31
    @52
    @33
    @3
    @34
    sqrtge0i
    ax-mp
    @36
    @53
    @38
    @5
    @39
    sqrtge0i
    ax-mp
    @4
    @6
    @35
    @40
    addge0i
    mp2an
    @7
    @50
    sqrtsqi
    ax-mp
    breqtri
    @48
    @8
    @2
    wceq
    @49
    @0
    normval
    ax-mp
    @9
    @4
    @10
    @6
    caddc
    @32
    @9
    @4
    wceq
    norm-ii.1
    cA
    normval
    ax-mp
    @37
    @10
    @6
    wceq
    norm-ii.2
    cB
    normval
    ax-mp
    oveq12i
    3brtr4i
end
