include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "crusgr.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "wi.mm"
include "simp1.mm"
include "anim1i.mm"
include "ancomd.mm"
include "simp3.mm"
include "simp2.mm"
include "jca.mm"
include "adantr.mm"
include "numclwwlk7lem.mm"
include "syl2anc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "cprime.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "cle.mm"
include "2z.mm"
include "a1i.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "wb.mm"
include "zltlem1.mm"
include "sylancr.mm"
include "biimpa.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "exprmfct.mm"
include "cclwwlkn.mm"
include "chash.mm"
include "cmo.mm"
include "cc0.mm"
include "cfusgr.mm"
include "finrusgrfusgr.mm"
include "3ad2ant3.mm"
include "simp1l.mm"
include "numclwwlk8.mm"
include "pm3.22.mm"
include "3adant1.mm"
include "numclwwlk7.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "ax-1ne0.mm"
include "nesymi.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "sylc.mm"
include "a1d.mm"
include "3exp.mm"
include "rexlimiva.mm"
include "mpcom.mm"
include "expcom.mm"
include "com23.mm"
include "wn.mm"
include "1red.mm"
include "nn0re.mm"
include "ltnled.mm"
include "1e2m1.mm"
include "breq2d.mm"
include "notbid.mm"
include "sylancl.mm"
include "bicomd.mm"
include "3bitrd.mm"
include "cr.mm"
include "2re.mm"
include "lttri3.mm"
include "biimprd.mm"
include "expd.mm"
include "sylbid.mm"
include "com3r.mm"
include "pm2.61i.mm"
include "mpd.mm"
include "expimpd.mm"

theorem frgrreggt1
  let cG: class G
  let cK: class K
  let cV: class V
  let vp: setvar p
  assume frgrreggt1.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ V e. Fin /\ V =/= (/) ) -> ( ( G RegUSGraph K /\ 1 < K ) -> K = 2 ) )

  proof
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    w3a
    #
    cG
    cK
    crusgr
    wbr
    #
    c1
    cK
    clt
    wbr
    #
    cK
    c2
    wceq
    #
    @3
    @4
    wa
    #
    cK
    cn0
    wcel
    #
    @5
    @6
    wi
    #
    @7
    @4
    @0
    wa
    #
    @2
    @1
    wa
    #
    @8
    @7
    @0
    @4
    @3
    @0
    @4
    @0
    @1
    @2
    simp1
    anim1i
    ancomd
    #
    @3
    @11
    @4
    @3
    @2
    @1
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    #
    jca
    adantr
    cG
    cK
    cV
    frgrreggt1.v
    numclwwlk7lem
    syl2anc
    c2
    cK
    clt
    wbr
    #
    @7
    @8
    @9
    wi
    #
    wi
    @14
    @8
    @7
    @9
    @8
    @14
    @7
    @9
    wi
    #
    vp
    cv
    #
    cK
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @8
    @14
    wa
    #
    @16
    @21
    @18
    c2
    cuz
    cfv
    wcel
    #
    @20
    @21
    c2
    cz
    wcel
    #
    @18
    cz
    wcel
    #
    c2
    @18
    cle
    wbr
    #
    @22
    @23
    @21
    2z
    a1i
    @21
    cK
    cz
    wcel
    #
    @24
    @8
    @26
    @14
    cK
    nn0z
    #
    adantr
    cK
    peano2zm
    syl
    @8
    @14
    @25
    @8
    @23
    @26
    @14
    @25
    wb
    2z
    @27
    c2
    cK
    zltlem1
    sylancr
    biimpa
    c2
    @18
    eluz2
    syl3anbrc
    @18
    vp
    exprmfct
    syl
    @19
    @21
    @16
    wi
    vp
    cprime
    @17
    cprime
    wcel
    #
    @19
    wa
    #
    @21
    @7
    @9
    @29
    @21
    @7
    w3a
    #
    @6
    @5
    @30
    @17
    cG
    cclwwlkn
    co
    chash
    cfv
    @17
    cmo
    co
    #
    cc0
    wceq
    #
    @31
    c1
    wceq
    #
    @6
    @30
    cG
    cfusgr
    wcel
    #
    @28
    @32
    @7
    @29
    @34
    @21
    @7
    @4
    @1
    wa
    @34
    @7
    @1
    @4
    @3
    @1
    @4
    @13
    anim1i
    ancomd
    cG
    cK
    cV
    frgrreggt1.v
    finrusgrfusgr
    syl
    3ad2ant3
    @28
    @19
    @21
    @7
    simp1l
    @17
    cG
    numclwwlk8
    syl2anc
    @30
    @10
    @11
    @29
    @33
    @7
    @29
    @10
    @21
    @12
    3ad2ant3
    @7
    @29
    @11
    @21
    @3
    @11
    @4
    @1
    @2
    @11
    @0
    @1
    @2
    pm3.22
    3adant1
    adantr
    3ad2ant3
    @29
    @21
    @7
    simp1
    @17
    cG
    cK
    cV
    frgrreggt1.v
    numclwwlk7
    syl3anc
    @32
    @33
    cc0
    c1
    wceq
    #
    @6
    @31
    cc0
    c1
    eqeq1
    @35
    @6
    c1
    cc0
    ax-1ne0
    nesymi
    pm2.21i
    syl6bi
    sylc
    a1d
    3exp
    rexlimiva
    mpcom
    expcom
    com23
    @14
    wn
    #
    @15
    @7
    @8
    @5
    @36
    @6
    @8
    @5
    cK
    c2
    clt
    wbr
    #
    wn
    #
    @36
    @6
    wi
    @8
    @5
    cK
    c1
    cle
    wbr
    #
    wn
    cK
    c2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    wn
    @38
    @8
    c1
    cK
    @8
    1red
    cK
    nn0re
    #
    ltnled
    @8
    @39
    @41
    @8
    c1
    @40
    cK
    cle
    c1
    @40
    wceq
    @8
    1e2m1
    a1i
    breq2d
    notbid
    @8
    @41
    @37
    @8
    @37
    @41
    @8
    @26
    @23
    @37
    @41
    wb
    @27
    2z
    cK
    c2
    zltlem1
    sylancl
    bicomd
    notbid
    3bitrd
    @8
    @38
    @36
    @6
    @8
    cK
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @38
    @36
    wa
    #
    @6
    wi
    @42
    2re
    @43
    @44
    wa
    @6
    @45
    cK
    c2
    lttri3
    biimprd
    sylancl
    expd
    sylbid
    com3r
    a1d
    pm2.61i
    mpd
    expimpd
end
