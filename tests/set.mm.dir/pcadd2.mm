include "cpc.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cxr.mm"
include "wcel.mm"
include "wi.mm"
include "cprime.mm"
include "cq.mm"
include "pcxcl.mm"
include "syl2anc.mm"
include "xrltle.mm"
include "mpd.mm"
include "pcadd.mm"
include "cneg.mm"
include "qaddcl.mm"
include "qnegcl.mm"
include "syl.mm"
include "wn.mm"
include "wb.mm"
include "xrltnle.mm"
include "mpbid.mm"
include "wa.mm"
include "adantr.mm"
include "pcneg.mm"
include "breq1d.mm"
include "biimpar.mm"
include "ex.mm"
include "cc0.mm"
include "cc.mm"
include "qcn.mm"
include "negcld.mm"
include "add12d.mm"
include "addcomd.mm"
include "negidd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "breq12d.mm"
include "sylibd.mm"
include "mtod.mm"
include "mpbird.mm"
include "breqtrrd.mm"
include "addassd.mm"
include "breqtrd.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem pcadd2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  assume pcadd2.1: |- ( ph -> P e. Prime )
  assume pcadd2.2: |- ( ph -> A e. QQ )
  assume pcadd2.3: |- ( ph -> B e. QQ )
  assume pcadd2.4: |- ( ph -> ( P pCnt A ) < ( P pCnt B ) )


  assert |- ( ph -> ( P pCnt A ) = ( P pCnt ( A + B ) ) )

  proof
    wph
    cP
    cA
    cpc
    co
    #
    cP
    cA
    cB
    caddc
    co
    #
    cpc
    co
    #
    wceq
    #
    @0
    @2
    cle
    wbr
    #
    @2
    @0
    cle
    wbr
    #
    wph
    cA
    cB
    cP
    pcadd2.1
    pcadd2.2
    pcadd2.3
    wph
    @0
    cP
    cB
    cpc
    co
    #
    clt
    wbr
    #
    @0
    @6
    cle
    wbr
    #
    pcadd2.4
    wph
    @0
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @7
    @8
    wi
    wph
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    #
    @9
    pcadd2.1
    pcadd2.2
    cP
    cA
    pcxcl
    syl2anc
    #
    wph
    @11
    cB
    cq
    wcel
    #
    @10
    pcadd2.1
    pcadd2.3
    cP
    cB
    pcxcl
    syl2anc
    #
    @0
    @6
    xrltle
    syl2anc
    mpd
    pcadd
    wph
    @2
    cP
    @1
    cB
    cneg
    #
    caddc
    co
    #
    cpc
    co
    @0
    cle
    wph
    @1
    @16
    cP
    pcadd2.1
    wph
    @12
    @14
    @1
    cq
    wcel
    #
    pcadd2.2
    pcadd2.3
    cA
    cB
    qaddcl
    syl2anc
    #
    wph
    @14
    @16
    cq
    wcel
    #
    pcadd2.3
    cB
    qnegcl
    syl
    #
    wph
    @2
    @6
    cP
    @16
    cpc
    co
    #
    cle
    wph
    @2
    @6
    clt
    wbr
    #
    @2
    @6
    cle
    wbr
    #
    wph
    @23
    @6
    @2
    cle
    wbr
    #
    wn
    #
    wph
    @25
    @6
    @0
    cle
    wbr
    #
    wph
    @7
    @27
    wn
    #
    pcadd2.4
    wph
    @9
    @10
    @7
    @28
    wb
    @13
    @15
    @0
    @6
    xrltnle
    syl2anc
    mpbid
    wph
    @25
    @22
    cP
    @16
    @1
    caddc
    co
    #
    cpc
    co
    #
    cle
    wbr
    #
    @27
    wph
    @25
    @31
    wph
    @25
    wa
    @16
    @1
    cP
    wph
    @11
    @25
    pcadd2.1
    adantr
    wph
    @20
    @25
    @21
    adantr
    wph
    @18
    @25
    @19
    adantr
    wph
    @22
    @2
    cle
    wbr
    @25
    wph
    @22
    @6
    @2
    cle
    wph
    @11
    @14
    @22
    @6
    wceq
    pcadd2.1
    pcadd2.3
    cB
    cP
    pcneg
    syl2anc
    #
    breq1d
    biimpar
    pcadd
    ex
    wph
    @22
    @6
    @30
    @0
    cle
    @32
    wph
    @29
    cA
    cP
    cpc
    wph
    @29
    cA
    @16
    cB
    caddc
    co
    #
    caddc
    co
    cA
    cc0
    caddc
    co
    #
    cA
    wph
    @16
    cA
    cB
    wph
    cB
    wph
    @14
    cB
    cc
    wcel
    pcadd2.3
    cB
    qcn
    syl
    #
    negcld
    #
    wph
    @12
    cA
    cc
    wcel
    pcadd2.2
    cA
    qcn
    syl
    #
    @35
    add12d
    wph
    @33
    cc0
    cA
    caddc
    wph
    @33
    cB
    @16
    caddc
    co
    #
    cc0
    wph
    @16
    cB
    @36
    @35
    addcomd
    wph
    cB
    @35
    negidd
    #
    eqtrd
    oveq2d
    wph
    cA
    @37
    addid1d
    #
    3eqtrd
    oveq2d
    breq12d
    sylibd
    mtod
    wph
    @2
    cxr
    wcel
    #
    @10
    @23
    @26
    wb
    wph
    @11
    @18
    @41
    pcadd2.1
    @19
    cP
    @1
    pcxcl
    syl2anc
    #
    @15
    @2
    @6
    xrltnle
    syl2anc
    mpbird
    wph
    @41
    @10
    @23
    @24
    wi
    @42
    @15
    @2
    @6
    xrltle
    syl2anc
    mpd
    @32
    breqtrrd
    pcadd
    wph
    @17
    cA
    cP
    cpc
    wph
    @17
    cA
    @38
    caddc
    co
    @34
    cA
    wph
    cA
    cB
    @16
    @37
    @35
    @36
    addassd
    wph
    @38
    cc0
    cA
    caddc
    @39
    oveq2d
    @40
    3eqtrd
    oveq2d
    breqtrd
    wph
    @9
    @41
    @3
    @4
    @5
    wa
    wb
    @13
    @42
    @0
    @2
    xrletri3
    syl2anc
    mpbir2and
end
