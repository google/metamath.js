include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "ccsh.mm"
include "wi.mm"
include "wceq.mm"
include "cmin.mm"
include "caddc.mm"
include "oveq1.mm"
include "eqcomd.mm"
include "ad2antrr.mm"
include "cword.mm"
include "cfz.mm"
include "cle.mm"
include "cprime.mm"
include "simpld.mm"
include "adantr.mm"
include "adantl.mm"
include "elfzofz.mm"
include "3ad2ant2.mm"
include "fznn0sub2.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "cn0.mm"
include "cn.mm"
include "elfzo0.mm"
include "cz.mm"
include "zre.mm"
include "nnre.mm"
include "nn0re.mm"
include "resubcl.mm"
include "syl2anr.mm"
include "readdcld.mm"
include "jca.mm"
include "ex.mm"
include "elfzoelz.mm"
include "syl11.mm"
include "3adant3.mm"
include "sylbi.mm"
include "imp.mm"
include "fzonmapblen.mm"
include "ltle.mm"
include "sylc.mm"
include "simpl.mm"
include "elfzelz.mm"
include "2cshw.mm"
include "syl3anc.mm"
include "syl13anc.mm"
include "2cshwid.mm"
include "sylan2.mm"
include "syl2an.mm"
include "3eqtr3d.mm"
include "c1.mm"
include "simplrl.mm"
include "simplrr.mm"
include "3simpa.mm"
include "nnz.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "anim2i.mm"
include "ancoms.mm"
include "zaddcl.mm"
include "elnn0z.mm"
include "simplr.mm"
include "wb.mm"
include "posdif.mm"
include "biimp3a.mm"
include "addgegt0d.mm"
include "com12.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "simp2bi.mm"
include "elfzo1.mm"
include "syl3anbrc.mm"
include "cshwshashlem1.mm"
include "pm2.21ddne.mm"
include "2a1.mm"
include "pm2.61ine.mm"

theorem cshwshashlem2
  let wph: wff ph
  let vi: setvar i
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vj: setvar j
  assume cshwshash.0: |- ( ph -> ( W e. Word V /\ ( # ` W ) e. Prime ) )

  disjoint L i
  disjoint V i
  disjoint W i
  disjoint i ph
  disjoint K i
  disjoint L j
  disjoint i j
  disjoint V j
  disjoint W j
  disjoint j ph
  assert |- ( ( ph /\ E. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) =/= ( W ` 0 ) ) -> ( ( L e. ( 0 ..^ ( # ` W ) ) /\ K e. ( 0 ..^ ( # ` W ) ) /\ K < L ) -> ( W cyclShift L ) =/= ( W cyclShift K ) ) )

  proof
    wph
    vi
    cv
    cW
    cfv
    cc0
    cW
    cfv
    wne
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wrex
    #
    wa
    #
    cL
    @1
    wcel
    #
    cK
    @1
    wcel
    #
    cK
    cL
    clt
    wbr
    #
    w3a
    #
    cW
    cL
    ccsh
    co
    #
    cW
    cK
    ccsh
    co
    #
    wne
    #
    wi
    #
    wi
    @8
    @9
    @8
    @9
    wceq
    #
    @3
    @11
    @12
    @3
    wa
    #
    @7
    @10
    @13
    @7
    wa
    #
    @10
    cW
    cK
    @0
    cL
    cmin
    co
    #
    caddc
    co
    #
    ccsh
    co
    #
    cW
    @14
    @9
    @15
    ccsh
    co
    #
    @8
    @15
    ccsh
    co
    #
    @17
    cW
    @12
    @18
    @19
    wceq
    @3
    @7
    @12
    @19
    @18
    @8
    @9
    @15
    ccsh
    oveq1
    eqcomd
    ad2antrr
    @14
    cW
    cV
    cword
    wcel
    #
    cK
    cc0
    @0
    cfz
    co
    #
    wcel
    #
    @15
    @21
    wcel
    #
    @16
    @0
    cle
    wbr
    #
    @18
    @17
    wceq
    #
    @13
    @20
    @7
    @3
    @20
    @12
    wph
    @20
    @2
    wph
    @20
    @0
    cprime
    wcel
    cshwshash.0
    simpld
    adantr
    adantl
    #
    adantr
    @7
    @22
    @13
    @5
    @4
    @22
    @6
    cK
    cc0
    @0
    elfzofz
    3ad2ant2
    adantl
    @7
    @23
    @13
    @4
    @5
    @23
    @6
    @4
    cL
    @21
    wcel
    #
    @23
    cL
    cc0
    @0
    elfzofz
    #
    cL
    @0
    fznn0sub2
    syl
    3ad2ant1
    adantl
    @7
    @24
    @13
    @7
    @16
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    #
    @16
    @0
    clt
    wbr
    #
    @24
    @4
    @5
    @31
    @6
    @4
    @5
    @31
    @4
    cL
    cn0
    wcel
    #
    @0
    cn
    wcel
    #
    cL
    @0
    clt
    wbr
    #
    w3a
    #
    @5
    @31
    wi
    #
    cL
    @0
    elfzo0
    #
    @33
    @34
    @37
    @35
    cK
    cz
    wcel
    #
    @33
    @34
    wa
    #
    @31
    @5
    @39
    @40
    @31
    @39
    @40
    wa
    #
    @29
    @30
    @41
    cK
    @15
    @39
    cK
    cr
    wcel
    #
    @40
    cK
    zre
    #
    adantr
    @40
    @15
    cr
    wcel
    #
    @39
    @34
    @30
    cL
    cr
    wcel
    #
    @44
    @33
    @0
    nnre
    #
    cL
    nn0re
    #
    @0
    cL
    resubcl
    syl2anr
    #
    adantl
    readdcld
    @40
    @30
    @39
    @34
    @30
    @33
    @46
    adantl
    adantl
    jca
    ex
    cK
    cc0
    @0
    elfzoelz
    #
    syl11
    3adant3
    sylbi
    imp
    3adant3
    cL
    cK
    @0
    fzonmapblen
    #
    @16
    @0
    ltle
    sylc
    adantl
    @20
    @22
    @23
    @24
    w3a
    #
    wa
    @20
    @39
    @15
    cz
    wcel
    #
    @25
    @20
    @51
    simpl
    @51
    @39
    @20
    @22
    @23
    @39
    @24
    cK
    cc0
    @0
    elfzelz
    3ad2ant1
    adantl
    @51
    @52
    @20
    @23
    @22
    @52
    @24
    @15
    cc0
    @0
    elfzelz
    3ad2ant2
    adantl
    cK
    @15
    cV
    cW
    2cshw
    syl3anc
    syl13anc
    @13
    @20
    @27
    @19
    cW
    wceq
    #
    @7
    @26
    @4
    @5
    @27
    @6
    @28
    3ad2ant1
    @27
    @20
    cL
    cz
    wcel
    #
    @53
    cL
    cc0
    @0
    elfzelz
    cL
    cV
    cW
    2cshwid
    sylan2
    syl2an
    3eqtr3d
    @14
    wph
    @2
    @16
    c1
    @0
    cfzo
    co
    wcel
    #
    @17
    cW
    wne
    @12
    wph
    @2
    @7
    simplrl
    @12
    wph
    @2
    @7
    simplrr
    @7
    @55
    @13
    @7
    @16
    cn
    wcel
    #
    @34
    @32
    @55
    @7
    @16
    cz
    wcel
    #
    cc0
    @16
    clt
    wbr
    #
    @56
    @4
    @5
    @57
    @6
    @4
    @40
    @39
    @57
    @5
    @4
    @36
    @40
    @38
    @33
    @34
    @35
    3simpa
    sylbi
    @49
    @40
    @39
    wa
    @39
    @52
    wa
    #
    @57
    @39
    @40
    @59
    @40
    @52
    @39
    @34
    @0
    cz
    wcel
    @54
    @52
    @33
    @0
    nnz
    cL
    nn0z
    @0
    cL
    zsubcl
    syl2anr
    anim2i
    ancoms
    cK
    @15
    zaddcl
    syl
    syl2an
    3adant3
    @4
    @5
    @58
    @6
    @4
    @5
    @58
    @4
    @36
    @5
    @58
    wi
    @38
    @5
    @36
    @58
    @5
    cK
    cn0
    wcel
    #
    @34
    cK
    @0
    clt
    wbr
    #
    w3a
    @36
    @58
    wi
    #
    cK
    @0
    elfzo0
    @60
    @34
    @62
    @61
    @60
    @39
    cc0
    cK
    cle
    wbr
    #
    wa
    #
    @62
    cK
    elnn0z
    @64
    @36
    @58
    @64
    @36
    wa
    cK
    @15
    @39
    @42
    @63
    @36
    @43
    ad2antrr
    @36
    @44
    @64
    @33
    @34
    @44
    @35
    @48
    3adant3
    adantl
    @39
    @63
    @36
    simplr
    @36
    cc0
    @15
    clt
    wbr
    #
    @64
    @33
    @34
    @35
    @65
    @33
    @45
    @30
    @35
    @65
    wb
    @34
    @47
    @46
    cL
    @0
    posdif
    syl2an
    biimp3a
    adantl
    addgegt0d
    ex
    sylbi
    3ad2ant1
    sylbi
    com12
    sylbi
    imp
    3adant3
    @16
    elnnz
    sylanbrc
    @4
    @5
    @34
    @6
    @4
    @33
    @34
    @35
    @38
    simp2bi
    3ad2ant1
    @50
    @0
    @16
    elfzo1
    syl3anbrc
    adantl
    wph
    vi
    @16
    cV
    cW
    cshwshash.0
    cshwshashlem1
    syl3anc
    pm2.21ddne
    ex
    ex
    @10
    @3
    @7
    2a1
    pm2.61ine
end
