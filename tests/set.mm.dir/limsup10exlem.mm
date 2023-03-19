include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wss.mm"
include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cif.mm"
include "wcel.mm"
include "cn.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "c0ex.mm"
include "prid1.mm"
include "cr.mm"
include "1re.mm"
include "elexi.mm"
include "prid2.mm"
include "ifcli.mm"
include "a1i.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "nfv.mm"
include "ifex.mm"
include "imassmpt.mm"
include "mpbird.mm"
include "cle.mm"
include "cceil.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "cz.mm"
include "ceilcld.mm"
include "1zzd.mm"
include "ifcld.mm"
include "adantr.mm"
include "simpr.mm"
include "2teven.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "2nn.mm"
include "cuz.mm"
include "eqid.mm"
include "zred.mm"
include "ceilged.mm"
include "letrd.mm"
include "iftrue.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "wn.mm"
include "leidi.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "eluzd.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "nnmulcld.mm"
include "fvmptd2.mm"
include "wfn.mm"
include "fnmpti.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "nnxrd.mm"
include "nnred.mm"
include "nleltd.mm"
include "ltled.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "crp.mm"
include "clt.mm"
include "nnrpd.mm"
include "2timesgt.mm"
include "syl.mm"
include "lelttrd.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "fnfvima2.mm"
include "eqeltrrd.mm"
include "caddc.mm"
include "2tp1odd.mm"
include "iffalsed.mm"
include "peano2nnd.mm"
include "rexri.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "prssd.mm"
include "eqssd.mm"

theorem limsup10exlem
  let wph: wff ph
  let vn: setvar n
  let cF: class F
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  assume limsup10exlem.1: |- F = ( n e. NN |-> if ( 2 || n , 0 , 1 ) )
  assume limsup10exlem.2: |- ( ph -> K e. RR )

  disjoint K n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( F " ( K [,) +oo ) ) = { 0 , 1 } )

  proof
    wph
    cF
    cK
    cpnf
    cico
    co
    #
    cima
    #
    cc0
    c1
    cpr
    #
    wph
    @1
    @2
    wss
    c2
    vn
    cv
    #
    cdvds
    wbr
    #
    cc0
    c1
    cif
    #
    @2
    wcel
    #
    vn
    cn
    @0
    cin
    #
    wral
    wph
    @6
    vn
    @7
    @6
    wph
    @3
    @7
    wcel
    wa
    #
    @4
    cc0
    c1
    @2
    cc0
    c1
    c0ex
    prid1
    cc0
    c1
    c1
    cr
    1re
    elexi
    #
    prid2
    ifcli
    a1i
    ralrimiva
    wph
    vn
    cn
    @5
    @0
    @2
    cF
    cvv
    wph
    vn
    nfv
    @5
    cvv
    wcel
    @8
    @4
    cc0
    c1
    c0ex
    @9
    ifex
    #
    a1i
    limsup10exlem.1
    imassmpt
    mpbird
    wph
    cc0
    c1
    @1
    wph
    c2
    c1
    cK
    cle
    wbr
    #
    cK
    cceil
    cfv
    #
    c1
    cif
    #
    cmul
    co
    #
    cF
    cfv
    cc0
    @1
    wph
    vn
    @14
    @5
    cc0
    cn
    cF
    cvv
    limsup10exlem.1
    wph
    @3
    @14
    wceq
    #
    wa
    #
    @4
    cc0
    c1
    @16
    @13
    cz
    wcel
    #
    @15
    @4
    wph
    @17
    @15
    wph
    @11
    @12
    c1
    cz
    wph
    cK
    limsup10exlem.2
    ceilcld
    #
    wph
    1zzd
    #
    ifcld
    #
    adantr
    wph
    @15
    simpr
    @13
    @3
    2teven
    syl2anc
    iftrued
    wph
    c2
    @13
    c2
    cn
    wcel
    wph
    2nn
    a1i
    wph
    @13
    c1
    cuz
    cfv
    #
    cn
    wph
    c1
    @13
    @21
    @21
    eqid
    @19
    @20
    wph
    @11
    c1
    @13
    cle
    wbr
    wph
    @11
    wa
    #
    c1
    @12
    @13
    cle
    @22
    c1
    cK
    @12
    c1
    cr
    wcel
    #
    @22
    1re
    a1i
    wph
    cK
    cr
    wcel
    #
    @11
    limsup10exlem.2
    adantr
    wph
    @12
    cr
    wcel
    @11
    wph
    @12
    @18
    zred
    adantr
    wph
    @11
    simpr
    wph
    cK
    @12
    cle
    wbr
    @11
    wph
    cK
    limsup10exlem.2
    ceilged
    adantr
    #
    letrd
    @11
    @13
    @12
    wceq
    wph
    @11
    @12
    c1
    iftrue
    adantl
    #
    breqtrrd
    wph
    @11
    wn
    #
    wa
    #
    c1
    c1
    @13
    cle
    c1
    c1
    cle
    wbr
    @28
    c1
    1re
    leidi
    a1i
    @27
    @13
    c1
    wceq
    wph
    @11
    @12
    c1
    iffalse
    adantl
    #
    breqtrrd
    pm2.61dan
    eluzd
    nnuz
    syl6eleqr
    #
    nnmulcld
    #
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    fvmptd2
    wph
    cn
    @14
    @0
    cF
    cF
    cn
    wfn
    wph
    vn
    cn
    @5
    cF
    @10
    limsup10exlem.1
    fnmpti
    a1i
    #
    @31
    wph
    cK
    cpnf
    @14
    wph
    cK
    limsup10exlem.2
    rexrd
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    @14
    @31
    nnxrd
    wph
    cK
    @14
    limsup10exlem.2
    wph
    @14
    @31
    nnred
    #
    wph
    cK
    @13
    @14
    limsup10exlem.2
    wph
    @13
    @30
    nnred
    @35
    wph
    @11
    cK
    @13
    cle
    wbr
    @22
    cK
    @12
    @13
    cle
    @25
    @26
    breqtrrd
    @28
    cK
    c1
    @13
    cle
    @28
    cK
    c1
    wph
    @24
    @27
    limsup10exlem.2
    adantr
    #
    @23
    @28
    1re
    a1i
    #
    @28
    cK
    c1
    @36
    @37
    wph
    @27
    simpr
    nleltd
    ltled
    @28
    @13
    c1
    @29
    eqcomd
    breqtrd
    pm2.61dan
    wph
    @13
    crp
    wcel
    @13
    @14
    clt
    wbr
    wph
    @13
    @30
    nnrpd
    @13
    2timesgt
    syl
    lelttrd
    #
    ltled
    wph
    @14
    @35
    ltpnfd
    elicod
    fnfvima2
    eqeltrrd
    wph
    @14
    c1
    caddc
    co
    #
    cF
    cfv
    c1
    @1
    wph
    vn
    @39
    @5
    c1
    cn
    cF
    cxr
    limsup10exlem.1
    wph
    @3
    @39
    wceq
    #
    wa
    #
    @4
    cc0
    c1
    @41
    @17
    @40
    @4
    wn
    wph
    @17
    @40
    @20
    adantr
    wph
    @40
    simpr
    @13
    @3
    2tp1odd
    syl2anc
    iffalsed
    wph
    @14
    @31
    peano2nnd
    #
    c1
    cxr
    wcel
    wph
    c1
    1re
    rexri
    a1i
    fvmptd2
    wph
    cn
    @39
    @0
    cF
    @32
    @42
    wph
    cK
    cpnf
    @39
    @33
    @34
    wph
    @39
    @42
    nnxrd
    wph
    cK
    @39
    limsup10exlem.2
    wph
    @39
    @42
    nnred
    #
    wph
    cK
    @14
    @39
    limsup10exlem.2
    @35
    @43
    @38
    wph
    @14
    @35
    ltp1d
    lttrd
    ltled
    wph
    @39
    @43
    ltpnfd
    elicod
    fnfvima2
    eqeltrrd
    prssd
    eqssd
end
