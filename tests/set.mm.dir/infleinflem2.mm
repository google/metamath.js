include "cmnf.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "mnflt.mm"
include "eqbrtrd.mm"
include "syl2anc.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "adantl.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "cxad.mm"
include "cle.mm"
include "cxr.mm"
include "id.mm"
include "sselda.mm"
include "cpnf.mm"
include "pnfxr.mm"
include "a1i.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "syl.mm"
include "sseldd.mm"
include "1re.mm"
include "rexri.mm"
include "xaddcld.mm"
include "w3a.mm"
include "oveq1.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "xaddmnf2.mm"
include "mp2an.mm"
include "eqtrd.mm"
include "mnfltd.mm"
include "adantlr.mm"
include "3adantl3.mm"
include "simpl2.mm"
include "simp2.mm"
include "2re.mm"
include "resubcld.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ltpnfd.mm"
include "xrlttrd.mm"
include "xrltned.mm"
include "xrred.mm"
include "caddc.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "1red.mm"
include "ltadd1dd.mm"
include "cc.mm"
include "recn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "wb.mm"
include "rexaddd.mm"
include "breq1d.mm"
include "mpbird.mm"
include "an32s.mm"
include "3adantl2.mm"
include "pm2.61dan.mm"
include "syl3anc.mm"
include "xrlelttrd.mm"
include "simpl3.mm"
include "mnfxr.mm"
include "syl6eqel.mm"
include "rexr.mm"
include "xrltnled.mm"
include "mpbid.mm"
include "3ad2antl1.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "jca31.mm"
include "simplr.mm"
include "simp-4r.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "ad4antr.mm"
include "ad3antlr.mm"
include "ad3antrrr.mm"
include "ltm1d.mm"
include "lttrd.mm"
include "lelttrd.mm"
include "syl21anc.mm"

theorem infleinflem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let cZ: class Z
  assume infleinflem2.a: |- ( ph -> A C_ RR* )
  assume infleinflem2.b: |- ( ph -> B C_ RR* )
  assume infleinflem2.r: |- ( ph -> R e. RR )
  assume infleinflem2.x: |- ( ph -> X e. B )
  assume infleinflem2.t: |- ( ph -> X < ( R - 2 ) )
  assume infleinflem2.z: |- ( ph -> Z e. A )
  assume infleinflem2.l: |- ( ph -> Z <_ ( X +e 1 ) )


  assert |- ( ph -> Z < R )

  proof
    wph
    cZ
    cmnf
    wceq
    #
    cZ
    cR
    clt
    wbr
    #
    wph
    @0
    wa
    cR
    cr
    wcel
    #
    @0
    @1
    wph
    @2
    @0
    infleinflem2.r
    adantr
    wph
    @0
    simpr
    @2
    @0
    wa
    cZ
    cmnf
    cR
    clt
    @2
    @0
    simpr
    @2
    cmnf
    cR
    clt
    wbr
    @0
    cR
    mnflt
    adantr
    eqbrtrd
    syl2anc
    wph
    @0
    wn
    #
    wa
    wph
    cZ
    cmnf
    wne
    #
    @1
    wph
    @3
    simpl
    @3
    @4
    wph
    cZ
    cmnf
    neqne
    adantl
    wph
    @4
    wa
    #
    @2
    cX
    cr
    wcel
    #
    wa
    #
    cX
    cR
    c2
    cmin
    co
    #
    clt
    wbr
    #
    wa
    #
    cZ
    cr
    wcel
    #
    cZ
    cX
    c1
    cxad
    co
    #
    cle
    wbr
    #
    @1
    @5
    @2
    @6
    @9
    wph
    @2
    @4
    infleinflem2.r
    adantr
    @5
    cX
    wph
    cX
    cxr
    wcel
    #
    @4
    wph
    wph
    cX
    cB
    wcel
    @14
    wph
    id
    #
    infleinflem2.x
    wph
    cB
    cxr
    cX
    infleinflem2.b
    sselda
    syl2anc
    #
    adantr
    #
    @5
    @11
    @14
    @13
    cX
    cmnf
    wne
    #
    @5
    cZ
    wph
    cZ
    cxr
    wcel
    #
    @4
    wph
    wph
    cZ
    cA
    wcel
    @19
    @15
    infleinflem2.z
    wph
    cA
    cxr
    cZ
    infleinflem2.a
    sselda
    syl2anc
    #
    adantr
    wph
    @4
    simpr
    wph
    cZ
    cpnf
    wne
    @4
    wph
    cZ
    cpnf
    @20
    cpnf
    cxr
    wcel
    #
    wph
    pnfxr
    a1i
    #
    wph
    cZ
    cR
    c1
    cmin
    co
    #
    cpnf
    @20
    wph
    @2
    @23
    cxr
    wcel
    infleinflem2.r
    @2
    @23
    cR
    peano2rem
    #
    rexrd
    syl
    #
    @22
    wph
    cZ
    @12
    @23
    @20
    wph
    @14
    @12
    cxr
    wcel
    wph
    cB
    cxr
    cX
    infleinflem2.b
    infleinflem2.x
    sseldd
    #
    @14
    cX
    c1
    @14
    id
    c1
    cxr
    wcel
    #
    @14
    c1
    1re
    rexri
    #
    a1i
    xaddcld
    syl
    @25
    infleinflem2.l
    wph
    @2
    @14
    @9
    @12
    @23
    clt
    wbr
    #
    infleinflem2.r
    @26
    infleinflem2.t
    @2
    @14
    @9
    w3a
    #
    cX
    cmnf
    wceq
    #
    @29
    @2
    @14
    @31
    @29
    @9
    @2
    @31
    @29
    @14
    @2
    @31
    wa
    @12
    cmnf
    @23
    clt
    @31
    @12
    cmnf
    wceq
    #
    @2
    @31
    @12
    cmnf
    c1
    cxad
    co
    #
    cmnf
    cX
    cmnf
    c1
    cxad
    oveq1
    @33
    cmnf
    wceq
    #
    @31
    @27
    c1
    cpnf
    wne
    #
    @34
    @28
    c1
    cr
    wcel
    #
    @35
    1re
    c1
    renepnf
    ax-mp
    c1
    xaddmnf2
    mp2an
    a1i
    eqtrd
    #
    adantl
    @2
    cmnf
    @23
    clt
    wbr
    @31
    @2
    @23
    @24
    mnfltd
    adantr
    eqbrtrd
    adantlr
    3adantl3
    @30
    @31
    wn
    #
    wa
    #
    @30
    @6
    @29
    @30
    @38
    simpl
    @39
    cX
    @2
    @14
    @9
    @38
    simpl2
    @38
    @18
    @30
    cX
    cmnf
    neqne
    adantl
    @30
    cX
    cpnf
    wne
    #
    @38
    @30
    cX
    cpnf
    @2
    @14
    @9
    simp2
    #
    @21
    @30
    pnfxr
    a1i
    #
    @30
    cX
    @8
    cpnf
    @41
    @2
    @14
    @8
    cxr
    wcel
    @9
    @2
    @8
    @2
    cR
    c2
    @2
    id
    #
    c2
    cr
    wcel
    @2
    2re
    a1i
    resubcld
    #
    rexrd
    3ad2ant1
    @42
    @2
    @14
    @9
    simp3
    @2
    @14
    @8
    cpnf
    clt
    wbr
    @9
    @2
    @8
    @44
    ltpnfd
    3ad2ant1
    xrlttrd
    xrltned
    #
    adantr
    xrred
    @2
    @9
    @6
    @29
    @14
    @2
    @6
    @9
    @29
    @10
    @29
    cX
    c1
    caddc
    co
    #
    @23
    clt
    wbr
    #
    @10
    @46
    @8
    c1
    caddc
    co
    #
    @23
    clt
    @10
    cX
    @8
    c1
    @6
    @6
    @2
    @9
    @6
    id
    #
    ad2antlr
    #
    @2
    @8
    cr
    wcel
    @6
    @9
    @44
    ad2antrr
    @10
    @6
    @36
    @50
    @6
    1red
    #
    syl
    @7
    @9
    simpr
    ltadd1dd
    @2
    @48
    @23
    wceq
    #
    @6
    @9
    @2
    cR
    cc
    wcel
    #
    @52
    cR
    recn
    @53
    cR
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @48
    @23
    @53
    cR
    c2
    c1
    @53
    id
    @53
    2cnd
    @53
    1cnd
    subsubd
    @55
    @23
    wceq
    @53
    @54
    c1
    cR
    cmin
    2m1e1
    oveq2i
    a1i
    eqtr3d
    syl
    ad2antrr
    breqtrd
    @6
    @29
    @47
    wb
    @2
    @9
    @6
    @12
    @46
    @23
    clt
    @6
    cX
    c1
    @49
    @51
    rexaddd
    #
    breq1d
    ad2antlr
    mpbird
    #
    an32s
    3adantl2
    syl2anc
    pm2.61dan
    syl3anc
    xrlelttrd
    wph
    @2
    @23
    cpnf
    clt
    wbr
    infleinflem2.r
    @2
    @23
    @24
    ltpnfd
    syl
    xrlttrd
    xrltned
    adantr
    xrred
    #
    @17
    wph
    @13
    @4
    infleinflem2.l
    adantr
    #
    @11
    @14
    @13
    w3a
    #
    cX
    cmnf
    @60
    @31
    @13
    @11
    @14
    @13
    @31
    simpl3
    @11
    @14
    @31
    @13
    wn
    #
    @13
    @11
    @31
    wa
    #
    @12
    cZ
    clt
    wbr
    @61
    @62
    @12
    cmnf
    cZ
    clt
    @31
    @32
    @11
    @37
    adantl
    #
    @11
    cmnf
    cZ
    clt
    wbr
    @31
    cZ
    mnflt
    adantr
    eqbrtrd
    @62
    @12
    cZ
    @62
    @12
    cmnf
    cxr
    @63
    mnfxr
    syl6eqel
    @11
    @19
    @31
    cZ
    rexr
    adantr
    xrltnled
    mpbid
    3ad2antl1
    pm2.65da
    neqned
    syl3anc
    wph
    @40
    @4
    wph
    @2
    @14
    @9
    @40
    infleinflem2.r
    @16
    infleinflem2.t
    @45
    syl3anc
    adantr
    xrred
    wph
    @9
    @4
    infleinflem2.t
    adantr
    jca31
    @58
    @59
    @10
    @11
    wa
    #
    @13
    wa
    #
    cZ
    @12
    cR
    @10
    @11
    @13
    simplr
    @65
    @6
    @12
    cr
    wcel
    #
    @2
    @6
    @9
    @11
    @13
    simp-4r
    @6
    @12
    @46
    cr
    @56
    @6
    cX
    c1
    @49
    @51
    readdcld
    eqeltrd
    #
    syl
    @2
    @2
    @6
    @9
    @11
    @13
    @43
    ad4antr
    @64
    @13
    simpr
    @64
    @12
    cR
    clt
    wbr
    @13
    @64
    @12
    @23
    cR
    @6
    @66
    @2
    @9
    @11
    @67
    ad3antlr
    @2
    @23
    cr
    wcel
    @6
    @9
    @11
    @24
    ad3antrrr
    @2
    @2
    @6
    @9
    @11
    @43
    ad3antrrr
    #
    @10
    @29
    @11
    @57
    adantr
    @64
    cR
    @68
    ltm1d
    lttrd
    adantr
    lelttrd
    syl21anc
    syl2anc
    pm2.61dan
end
