include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "c2.mm"
include "cexp.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "simpl.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "cn.mm"
include "prmnn.mm"
include "adantr.mm"
include "prmz.mm"
include "fzoval.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "jca.mm"
include "fzm1ndvds.mm"
include "w3a.mm"
include "eqid.mm"
include "modprminv.mm"
include "simpld.mm"
include "simprd.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "mp1i.mm"
include "sseld.mm"
include "3ad2ant1.mm"
include "imdistani.mm"
include "modprminveq.mm"
include "eqcomd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "reu8.mm"
include "sylibr.mm"

theorem reumodprminv
  let cP: class P
  let vi: setvar i
  let cN: class N
  let vs: setvar s

  disjoint N i
  disjoint P i
  disjoint N s
  disjoint i s
  disjoint P s
  assert |- ( ( P e. Prime /\ N e. ( 1 ..^ P ) ) -> E! i e. ( 1 ... ( P - 1 ) ) ( ( N x. i ) mod P ) = 1 )

  proof
    cP
    cprime
    wcel
    #
    cN
    c1
    cP
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cN
    vi
    cv
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    cN
    vs
    cv
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    vi
    vs
    weq
    #
    wi
    #
    vs
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    vi
    @15
    wrex
    #
    @7
    vi
    @15
    wreu
    @3
    cN
    cP
    c2
    cmin
    co
    cexp
    co
    cP
    cmo
    co
    #
    @15
    wcel
    #
    cN
    @19
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    @11
    @19
    @8
    wceq
    #
    wi
    #
    vs
    @15
    wral
    #
    wa
    #
    wa
    #
    @18
    @3
    @0
    cN
    cz
    wcel
    #
    cP
    cN
    cdvds
    wbr
    wn
    #
    @28
    @0
    @2
    simpl
    @2
    @29
    @0
    cN
    c1
    cP
    elfzoelz
    adantl
    @3
    cP
    cn
    wcel
    #
    cN
    @15
    wcel
    #
    wa
    @30
    @3
    @31
    @32
    @0
    @31
    @2
    cP
    prmnn
    adantr
    @0
    @2
    @32
    @0
    @1
    @15
    cN
    @0
    cP
    cz
    wcel
    @1
    @15
    wceq
    cP
    prmz
    c1
    cP
    fzoval
    syl
    eleq2d
    biimpa
    jca
    cP
    cN
    fzm1ndvds
    syl
    @0
    @29
    @30
    w3a
    #
    @20
    @27
    @33
    @20
    @23
    cN
    cP
    @19
    @19
    eqid
    #
    modprminv
    #
    simpld
    @33
    @23
    @26
    @33
    @20
    @23
    @35
    simprd
    @33
    @25
    vs
    @15
    @33
    @8
    @15
    wcel
    #
    wa
    @33
    @8
    cc0
    @14
    cfz
    co
    #
    wcel
    #
    wa
    @25
    @33
    @36
    @38
    @0
    @29
    @36
    @38
    wi
    @30
    @0
    @15
    @37
    @8
    c1
    cc0
    cuz
    cfv
    wcel
    @15
    @37
    wss
    @0
    1eluzge0
    c1
    cc0
    @14
    fzss1
    mp1i
    sseld
    3ad2ant1
    imdistani
    @33
    @38
    @11
    @24
    @33
    @38
    @11
    wa
    #
    wa
    @8
    @19
    @33
    @39
    @8
    @19
    wceq
    cN
    cP
    @19
    @8
    @34
    modprminveq
    biimpa
    eqcomd
    expr
    syl
    ralrimiva
    jca
    jca
    syl3anc
    @17
    @27
    vi
    @19
    @15
    @4
    @19
    wceq
    #
    @7
    @23
    @16
    @26
    @40
    @6
    @22
    c1
    @40
    @5
    @21
    cP
    cmo
    @4
    @19
    cN
    cmul
    oveq2
    oveq1d
    eqeq1d
    @40
    @13
    @25
    vs
    @15
    @40
    @12
    @24
    @11
    @4
    @19
    @8
    eqeq1
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl
    @7
    @11
    vi
    vs
    @15
    @12
    @6
    @10
    c1
    @12
    @5
    @9
    cP
    cmo
    @4
    @8
    cN
    cmul
    oveq2
    oveq1d
    eqeq1d
    reu8
    sylibr
end
