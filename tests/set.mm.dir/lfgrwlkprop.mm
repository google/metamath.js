include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "cvtx.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "wlkv.mm"
include "eqid.mm"
include "iswlk.mm"
include "syl.mm"
include "wa.mm"
include "ifptru.mm"
include "adantr.mm"
include "simplr.mm"
include "wrdsymbcl.mm"
include "ad4ant14.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrab.mm"
include "fvex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "breq2i.mm"
include "clt.mm"
include "1lt2.mm"
include "wn.mm"
include "1re.mm"
include "2re.mm"
include "ltnlei.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "com12.mm"
include "adantl.mm"
include "a1i.mm"
include "syl5bi.mm"
include "mpd.mm"
include "sylbid.mm"
include "ex.mm"
include "neqne.mm"
include "2a1d.mm"
include "pm2.61i.mm"
include "ralimdva.mm"
include "com23.mm"
include "3impia.mm"
include "pm2.43i.mm"
include "imp.mm"

theorem lfgrwlkprop
  let vx: setvar x
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume lfgrwlkprop.i: |- I = ( iEdg ` G )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint G k
  disjoint I k
  disjoint I x
  disjoint P k
  disjoint V k
  disjoint V x
  assert |- ( ( F ( Walks ` G ) P /\ I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } ) -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cI
    cdm
    #
    c2
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    crab
    #
    cI
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @8
    c1
    caddc
    co
    cP
    cfv
    #
    wne
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @0
    @7
    @14
    wi
    #
    @0
    @0
    cF
    @1
    cword
    wcel
    #
    cc0
    @12
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @9
    @10
    wceq
    #
    @8
    cF
    cfv
    #
    cI
    cfv
    #
    @9
    csn
    #
    wceq
    #
    @9
    @10
    cpr
    @21
    wss
    #
    wif
    #
    vk
    @13
    wral
    #
    w3a
    #
    @15
    @0
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    @0
    @27
    wb
    cP
    cF
    cG
    wlkv
    cP
    cvv
    vk
    cF
    cG
    cI
    @17
    cvv
    cvv
    @17
    eqid
    lfgrwlkprop.i
    iswlk
    syl
    @16
    @18
    @26
    @15
    @16
    @18
    wa
    #
    @7
    @26
    @14
    @28
    @7
    @26
    @14
    wi
    @28
    @7
    wa
    #
    @25
    @11
    vk
    @13
    @19
    @29
    @8
    @13
    wcel
    #
    wa
    #
    @25
    @11
    wi
    #
    wi
    @19
    @31
    @32
    @19
    @31
    wa
    @25
    @23
    @11
    @19
    @25
    @23
    wb
    @31
    @19
    @23
    @24
    ifptru
    adantr
    @31
    @23
    @11
    wi
    #
    @19
    @31
    @21
    @6
    wcel
    #
    @33
    @31
    @1
    @6
    @20
    cI
    @28
    @7
    @30
    simplr
    @16
    @30
    @20
    @1
    wcel
    @18
    @7
    @8
    @1
    cF
    wrdsymbcl
    ad4ant14
    ffvelrnd
    @34
    @21
    @5
    wcel
    #
    c2
    @21
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @31
    @33
    @4
    @37
    vx
    @21
    @5
    @2
    @21
    wceq
    @3
    @36
    c2
    cle
    @2
    @21
    chash
    fveq2
    breq2d
    elrab
    @38
    @33
    wi
    @31
    @37
    @33
    @35
    @23
    @37
    @11
    @23
    @37
    c2
    @22
    chash
    cfv
    #
    cle
    wbr
    #
    @11
    @23
    @36
    @39
    c2
    cle
    @21
    @22
    chash
    fveq2
    breq2d
    @40
    c2
    c1
    cle
    wbr
    #
    @11
    @39
    c1
    c2
    cle
    @9
    cvv
    wcel
    @39
    c1
    wceq
    @8
    cP
    fvex
    @9
    cvv
    hashsng
    ax-mp
    breq2i
    c1
    c2
    clt
    wbr
    #
    @41
    @11
    wi
    #
    1lt2
    @42
    @41
    wn
    @43
    c1
    c2
    1re
    2re
    ltnlei
    @41
    @11
    pm2.21
    sylbi
    ax-mp
    sylbi
    syl6bi
    com12
    adantl
    a1i
    syl5bi
    mpd
    adantl
    sylbid
    ex
    @19
    wn
    @11
    @31
    @25
    @9
    @10
    neqne
    2a1d
    pm2.61i
    ralimdva
    ex
    com23
    3impia
    syl6bi
    pm2.43i
    imp
end
