include "cewlks.mm"
include "co.mm"
include "wcel.mm"
include "cupgr.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cle.mm"
include "cvv.mm"
include "cxnn0.mm"
include "wa.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "cmin.mm"
include "cin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "ewlkprop.mm"
include "fvex.mm"
include "hashin.mm"
include "ax-mp.mm"
include "wfn.mm"
include "simpl3.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "funfn.mm"
include "sylib.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "cc0.mm"
include "simpl.mm"
include "cfz.mm"
include "elfzofz.mm"
include "fz1fzo0m1.mm"
include "adantl.mm"
include "jca.mm"
include "wrdsymbcl.mm"
include "3ad2antl2.mm"
include "cvtx.mm"
include "upgrle.mm"
include "syl3anc.mm"
include "cxr.mm"
include "inex1.mm"
include "hashxrcl.mm"
include "2re.mm"
include "rexri.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "xrletr.mm"
include "mpan2d.mm"
include "mpi.mm"
include "xnn0xr.mm"
include "expcomd.mm"
include "3ad2ant1.mm"
include "mpd.mm"
include "ralimdva.mm"
include "3exp.mm"
include "com34.mm"
include "3imp.mm"
include "cn0.mm"
include "lencl.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cz.mm"
include "wb.mm"
include "1zzd.mm"
include "nn0z.mm"
include "fzon.mm"
include "bicomd.mm"
include "cr.mm"
include "nn0re.mm"
include "1red.mm"
include "lenlt.mm"
include "bitrd.mm"
include "biimpd.mm"
include "necon2ad.mm"
include "impcom.mm"
include "rspn0.mm"
include "ex.mm"
include "com23.mm"
include "com13.mm"
include "3ad2ant2.mm"
include "syld.mm"
include "3imp21.mm"

theorem upgrewlkle2
  let cS: class S
  let cF: class F
  let cG: class G
  let vk: setvar k
  let cT: class T


  assert |- ( ( G e. UPGraph /\ F e. ( G EdgWalks S ) /\ 1 < ( # ` F ) ) -> S <_ 2 )

  proof
    cF
    cG
    cS
    cewlks
    co
    wcel
    #
    cG
    cupgr
    wcel
    #
    c1
    cF
    chash
    cfv
    #
    clt
    wbr
    #
    cS
    c2
    cle
    wbr
    #
    @0
    cG
    cvv
    wcel
    #
    cS
    cxnn0
    wcel
    #
    wa
    #
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    #
    cF
    cfv
    #
    @8
    cfv
    #
    @11
    cF
    cfv
    @8
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    c1
    @2
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @1
    @3
    @4
    wi
    #
    wi
    cS
    vk
    cF
    cG
    @8
    @8
    eqid
    #
    ewlkprop
    @21
    @1
    @4
    vk
    @19
    wral
    #
    @22
    @7
    @10
    @20
    @1
    @24
    wi
    @7
    @10
    @1
    @20
    @24
    @7
    @10
    @1
    @20
    @24
    wi
    @7
    @10
    @1
    w3a
    #
    @18
    @4
    vk
    @19
    @25
    @11
    @19
    wcel
    #
    wa
    #
    @17
    c2
    cle
    wbr
    #
    @18
    @4
    wi
    #
    @27
    @17
    @14
    chash
    cfv
    #
    cle
    wbr
    #
    @28
    @14
    cvv
    wcel
    #
    @31
    @13
    @8
    fvex
    #
    @14
    @15
    cvv
    hashin
    ax-mp
    @27
    @31
    @30
    c2
    cle
    wbr
    #
    @28
    @27
    @1
    @8
    @9
    wfn
    #
    @13
    @9
    wcel
    #
    @34
    @7
    @10
    @1
    @26
    simpl3
    @25
    @35
    @26
    @1
    @7
    @35
    @10
    @1
    @8
    wfun
    #
    @35
    @1
    cG
    cuhgr
    wcel
    @37
    cG
    upgruhgr
    @8
    cG
    @23
    uhgrfun
    syl
    @8
    funfn
    sylib
    3ad2ant3
    adantr
    @10
    @7
    @26
    @36
    @1
    @10
    @26
    wa
    #
    @10
    @12
    cc0
    @2
    cfzo
    co
    wcel
    #
    wa
    @36
    @38
    @10
    @39
    @10
    @26
    simpl
    @26
    @39
    @10
    @26
    @11
    c1
    @2
    cfz
    co
    wcel
    @39
    @11
    c1
    @2
    elfzofz
    @11
    @2
    fz1fzo0m1
    syl
    adantl
    jca
    @12
    @9
    cF
    wrdsymbcl
    syl
    3ad2antl2
    @9
    @8
    @13
    cG
    cG
    cvtx
    cfv
    #
    @40
    eqid
    @23
    upgrle
    syl3anc
    @27
    @17
    cxr
    wcel
    #
    @30
    cxr
    wcel
    #
    c2
    cxr
    wcel
    #
    w3a
    #
    @31
    @34
    wa
    @28
    wi
    @44
    @27
    @41
    @42
    @43
    @16
    cvv
    wcel
    @41
    @14
    @15
    @33
    inex1
    @16
    cvv
    hashxrcl
    ax-mp
    #
    @32
    @42
    @33
    @14
    cvv
    hashxrcl
    ax-mp
    c2
    2re
    rexri
    #
    3pm3.2i
    a1i
    @17
    @30
    c2
    xrletr
    syl
    mpan2d
    mpi
    @25
    @28
    @29
    wi
    #
    @26
    @7
    @10
    @47
    @1
    @6
    @47
    @5
    @6
    @18
    @28
    @4
    @6
    cS
    cxr
    wcel
    @41
    @43
    @18
    @28
    wa
    @4
    wi
    cS
    xnn0xr
    @41
    @6
    @45
    a1i
    @43
    @6
    @46
    a1i
    cS
    @17
    c2
    xrletr
    syl3anc
    expcomd
    adantl
    3ad2ant1
    adantr
    mpd
    ralimdva
    3exp
    com34
    3imp
    @10
    @7
    @24
    @22
    wi
    #
    @20
    @10
    @2
    cn0
    wcel
    #
    @48
    @9
    cF
    lencl
    @49
    @48
    wi
    @10
    @3
    @24
    @49
    @4
    @3
    @49
    @24
    @4
    @3
    @49
    @24
    @4
    wi
    #
    @3
    @49
    wa
    @19
    c0
    wne
    #
    @50
    @49
    @3
    @51
    @49
    @3
    @19
    c0
    @49
    @19
    c0
    wceq
    #
    @3
    wn
    #
    @49
    @52
    @2
    c1
    cle
    wbr
    #
    @53
    @49
    @54
    @52
    @49
    c1
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    @54
    @52
    wb
    @49
    @55
    @56
    @49
    1zzd
    @2
    nn0z
    jca
    c1
    @2
    fzon
    syl
    bicomd
    @49
    @2
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    @54
    @53
    wb
    @49
    @57
    @58
    @2
    nn0re
    @49
    1red
    jca
    @2
    c1
    lenlt
    syl
    bitrd
    biimpd
    necon2ad
    impcom
    @4
    vk
    @19
    rspn0
    syl
    ex
    com23
    com13
    a1i
    mpd
    3ad2ant2
    syld
    syl
    3imp21
end
