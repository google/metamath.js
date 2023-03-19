include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ciccp.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "cres.mm"
include "cxr.mm"
include "cmap.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "peano2nn.mm"
include "iccpart.mm"
include "syl.mm"
include "wss.mm"
include "simpl.mm"
include "cuz.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzss2.mm"
include "elmapssres.mm"
include "syl2anr.mm"
include "wi.mm"
include "fzoss2.mm"
include "ssralv.mm"
include "adantld.mm"
include "imp.mm"
include "wceq.mm"
include "fzossfz.mm"
include "a1i.mm"
include "sselda.mm"
include "fvres.mm"
include "eqcomd.mm"
include "simpr.mm"
include "elfzouz.mm"
include "adantl.mm"
include "fzofzp1b.mm"
include "mpbid.mm"
include "breq12d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "ex.mm"
include "adantr.mm"
include "impcom.mm"
include "mpd.mm"
include "mpbir2and.mm"
include "sylbid.mm"

theorem iccpartres
  let cP: class P
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. NN /\ P e. ( RePart ` ( M + 1 ) ) ) -> ( P |` ( 0 ... M ) ) e. ( RePart ` M ) )

  proof
    cM
    cn
    wcel
    #
    cP
    cM
    c1
    caddc
    co
    #
    ciccp
    cfv
    wcel
    #
    cP
    cc0
    cM
    cfz
    co
    #
    cres
    #
    cM
    ciccp
    cfv
    wcel
    #
    @0
    @2
    cP
    cxr
    cc0
    @1
    cfz
    co
    #
    cmap
    co
    wcel
    #
    vi
    cv
    #
    cP
    cfv
    #
    @8
    c1
    caddc
    co
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    wa
    #
    @5
    @0
    @1
    cn
    wcel
    @2
    @15
    wb
    cM
    peano2nn
    cP
    vi
    @1
    iccpart
    syl
    @0
    @15
    @5
    @0
    @15
    wa
    #
    @5
    @4
    cxr
    @3
    cmap
    co
    wcel
    #
    @8
    @4
    cfv
    #
    @10
    @4
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    @15
    @7
    @3
    @6
    wss
    #
    @17
    @0
    @7
    @14
    simpl
    @0
    @1
    cM
    cuz
    cfv
    #
    wcel
    #
    @23
    @0
    cM
    @24
    wcel
    #
    @25
    @0
    cM
    cz
    wcel
    @26
    cM
    nnz
    cM
    uzid
    syl
    cM
    cM
    peano2uz
    syl
    #
    cM
    cc0
    @1
    fzss2
    syl
    cP
    cxr
    @6
    @3
    elmapssres
    syl2anr
    @16
    @12
    vi
    @21
    wral
    #
    @22
    @0
    @15
    @28
    @0
    @14
    @28
    @7
    @0
    @21
    @13
    wss
    #
    @14
    @28
    wi
    @0
    @25
    @29
    @27
    cM
    cc0
    @1
    fzoss2
    syl
    @12
    vi
    @21
    @13
    ssralv
    syl
    adantld
    imp
    @15
    @0
    @28
    @22
    wi
    #
    @7
    @0
    @30
    wi
    @14
    @7
    @0
    @30
    @7
    @0
    wa
    #
    @12
    @20
    vi
    @21
    @31
    @8
    @21
    wcel
    #
    wa
    #
    @12
    @20
    @33
    @9
    @18
    @11
    @19
    clt
    @33
    @8
    @3
    wcel
    #
    @9
    @18
    wceq
    @31
    @21
    @3
    @8
    @21
    @3
    wss
    @31
    cc0
    cM
    fzossfz
    a1i
    sselda
    @34
    @18
    @9
    @8
    @3
    cP
    fvres
    eqcomd
    syl
    @33
    @19
    @11
    @33
    @10
    @3
    wcel
    #
    @19
    @11
    wceq
    @33
    @32
    @35
    @31
    @32
    simpr
    @33
    @8
    cc0
    cuz
    cfv
    wcel
    #
    @32
    @35
    wb
    @32
    @36
    @31
    @8
    cc0
    cM
    elfzouz
    adantl
    cc0
    cM
    @8
    fzofzp1b
    syl
    mpbid
    @10
    @3
    cP
    fvres
    syl
    eqcomd
    breq12d
    biimpd
    ralimdva
    ex
    adantr
    impcom
    mpd
    @0
    @5
    @17
    @22
    wa
    wb
    @15
    @4
    vi
    cM
    iccpart
    adantr
    mpbir2and
    ex
    sylbid
    imp
end
