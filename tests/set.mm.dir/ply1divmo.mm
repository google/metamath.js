include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wrmo.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "cif.mm"
include "w3a.mm"
include "cgrp.mm"
include "crg.mm"
include "adantr.mm"
include "ply1ring.mm"
include "syl.mm"
include "ringgrp.mm"
include "simprl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "simprr.mm"
include "deg1xrcl.mm"
include "ifcld.mm"
include "3jca.mm"
include "deg1suble.mm"
include "wb.mm"
include "xrmaxlt.mm"
include "biimpar.mm"
include "jca.mm"
include "xrlelttr.mm"
include "sylc.mm"
include "ex.mm"
include "wne.mm"
include "wn.mm"
include "caddc.mm"
include "cr.mm"
include "cn0.mm"
include "deg1nn0cl.mm"
include "ad2antrr.mm"
include "nn0red.mm"
include "wceq.mm"
include "grpsubeq0.mm"
include "equcom.mm"
include "syl6bb.mm"
include "necon3bid.mm"
include "nn0addge1.mm"
include "syl2anc.mm"
include "cco1.mm"
include "deg1mul2.mm"
include "breqtrrd.mm"
include "cabl.mm"
include "ringabl.mm"
include "ablnnncan1.mm"
include "ringsubdi.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "xrlenlt.mm"
include "mpbid.mm"
include "necon4ad.mm"
include "syld.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem ply1divmo
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let cE: class E
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let c.0: class .0.
  let vq: setvar q
  let vr: setvar r
  assume ply1divalg.p: |- P = ( Poly1 ` R )
  assume ply1divalg.d: |- D = ( deg1 ` R )
  assume ply1divalg.b: |- B = ( Base ` P )
  assume ply1divalg.m: |- .- = ( -g ` P )
  assume ply1divalg.z: |- .0. = ( 0g ` P )
  assume ply1divalg.t: |- .xb = ( .r ` P )
  assume ply1divalg.r1: |- ( ph -> R e. Ring )
  assume ply1divalg.f: |- ( ph -> F e. B )
  assume ply1divalg.g1: |- ( ph -> G e. B )
  assume ply1divalg.g2: |- ( ph -> G =/= .0. )
  assume ply1divmo.g3: |- ( ph -> ( ( coe1 ` G ) ` ( D ` G ) ) e. E )
  assume ply1divmo.e: |- E = ( RLReg ` R )

  disjoint ph q
  disjoint B q
  disjoint D q
  disjoint F q
  disjoint G q
  disjoint .- q
  disjoint .xb q
  disjoint ph r
  disjoint q r
  disjoint B r
  disjoint D r
  disjoint F r
  disjoint G r
  disjoint .- r
  disjoint .xb r
  assert |- ( ph -> E* q e. B ( D ` ( F .- ( G .xb q ) ) ) < ( D ` G ) )

  proof
    wph
    cF
    cG
    vq
    cv
    #
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    clt
    wbr
    #
    cF
    cG
    vr
    cv
    #
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    vq
    vr
    weq
    #
    wi
    #
    vr
    cB
    wral
    vq
    cB
    wral
    @5
    vq
    cB
    wrmo
    wph
    @13
    vq
    vr
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    @11
    @2
    @8
    c.mi
    co
    #
    cD
    cfv
    #
    @4
    clt
    wbr
    #
    @12
    @17
    @11
    @20
    @17
    @11
    wa
    #
    @19
    cxr
    wcel
    #
    @3
    @9
    cle
    wbr
    #
    @9
    @3
    cif
    #
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    w3a
    #
    @19
    @24
    cle
    wbr
    #
    @24
    @4
    clt
    wbr
    #
    wa
    @20
    @17
    @27
    @11
    @17
    @22
    @25
    @26
    @17
    @18
    cB
    wcel
    #
    @22
    @17
    cP
    cgrp
    wcel
    #
    @2
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @30
    @17
    cP
    crg
    wcel
    #
    @31
    @17
    cR
    crg
    wcel
    #
    @34
    wph
    @35
    @16
    ply1divalg.r1
    adantr
    #
    cP
    cR
    ply1divalg.p
    ply1ring
    syl
    #
    cP
    ringgrp
    syl
    #
    @17
    @31
    cF
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @32
    @38
    wph
    @39
    @16
    ply1divalg.f
    adantr
    #
    @17
    @34
    cG
    cB
    wcel
    #
    @14
    @40
    @37
    wph
    @42
    @16
    ply1divalg.g1
    adantr
    #
    wph
    @14
    @15
    simprl
    #
    cB
    cP
    c.xb
    cG
    @0
    ply1divalg.b
    ply1divalg.t
    ringcl
    syl3anc
    #
    cB
    cP
    c.mi
    cF
    @1
    ply1divalg.b
    ply1divalg.m
    grpsubcl
    syl3anc
    #
    @17
    @31
    @39
    @7
    cB
    wcel
    #
    @33
    @38
    @41
    @17
    @34
    @42
    @15
    @47
    @37
    @43
    wph
    @14
    @15
    simprr
    #
    cB
    cP
    c.xb
    cG
    @6
    ply1divalg.b
    ply1divalg.t
    ringcl
    syl3anc
    #
    cB
    cP
    c.mi
    cF
    @7
    ply1divalg.b
    ply1divalg.m
    grpsubcl
    syl3anc
    #
    cB
    cP
    c.mi
    @2
    @8
    ply1divalg.b
    ply1divalg.m
    grpsubcl
    syl3anc
    cB
    cD
    cP
    cR
    @18
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    deg1xrcl
    syl
    #
    @17
    @23
    @9
    @3
    cxr
    @17
    @33
    @9
    cxr
    wcel
    #
    @50
    cB
    cD
    cP
    cR
    @8
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    deg1xrcl
    syl
    #
    @17
    @32
    @3
    cxr
    wcel
    #
    @46
    cB
    cD
    cP
    cR
    @2
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    deg1xrcl
    syl
    #
    ifcld
    @17
    @42
    @26
    @43
    cB
    cD
    cP
    cR
    cG
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    deg1xrcl
    syl
    #
    3jca
    adantr
    @21
    @28
    @29
    @17
    @28
    @11
    @17
    cB
    cD
    cR
    @2
    @8
    c.mi
    cP
    ply1divalg.p
    ply1divalg.d
    @36
    ply1divalg.b
    ply1divalg.m
    @46
    @50
    deg1suble
    adantr
    @17
    @29
    @11
    @17
    @54
    @52
    @26
    @29
    @11
    wb
    @55
    @53
    @56
    @3
    @9
    @4
    xrmaxlt
    syl3anc
    biimpar
    jca
    @19
    @24
    @4
    xrlelttr
    sylc
    ex
    @17
    @20
    @0
    @6
    @17
    @0
    @6
    wne
    #
    @20
    wn
    #
    @17
    @57
    wa
    #
    @4
    @19
    cle
    wbr
    #
    @58
    @59
    @4
    cG
    @6
    @0
    c.mi
    co
    #
    c.xb
    co
    #
    cD
    cfv
    #
    @19
    cle
    @59
    @4
    @4
    @61
    cD
    cfv
    #
    caddc
    co
    #
    @63
    cle
    @59
    @4
    cr
    wcel
    @64
    cn0
    wcel
    #
    @4
    @65
    cle
    wbr
    @59
    @4
    wph
    @4
    cn0
    wcel
    #
    @16
    @57
    wph
    @35
    @42
    cG
    c.0
    wne
    #
    @67
    ply1divalg.r1
    ply1divalg.g1
    ply1divalg.g2
    cB
    cD
    cP
    cR
    cG
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divalg.z
    ply1divalg.b
    deg1nn0cl
    syl3anc
    ad2antrr
    nn0red
    @59
    @35
    @61
    cB
    wcel
    #
    @61
    c.0
    wne
    #
    @66
    wph
    @35
    @16
    @57
    ply1divalg.r1
    ad2antrr
    #
    @17
    @69
    @57
    @17
    @31
    @15
    @14
    @69
    @38
    @48
    @44
    cB
    cP
    c.mi
    @6
    @0
    ply1divalg.b
    ply1divalg.m
    grpsubcl
    syl3anc
    adantr
    #
    @17
    @70
    @57
    @17
    @61
    c.0
    @0
    @6
    @17
    @61
    c.0
    wceq
    #
    vr
    vq
    weq
    #
    @12
    @17
    @31
    @15
    @14
    @73
    @74
    wb
    @38
    @48
    @44
    cB
    cP
    c.mi
    @6
    @0
    c.0
    ply1divalg.b
    ply1divalg.z
    ply1divalg.m
    grpsubeq0
    syl3anc
    vr
    vq
    equcom
    syl6bb
    necon3bid
    biimpar
    #
    cB
    cD
    cP
    cR
    @61
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divalg.z
    ply1divalg.b
    deg1nn0cl
    syl3anc
    @4
    @64
    nn0addge1
    syl2anc
    @59
    cB
    cD
    cP
    cR
    c.xb
    cE
    cG
    @61
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divmo.e
    ply1divalg.b
    ply1divalg.t
    ply1divalg.z
    @71
    wph
    @42
    @16
    @57
    ply1divalg.g1
    ad2antrr
    wph
    @68
    @16
    @57
    ply1divalg.g2
    ad2antrr
    wph
    @4
    cG
    cco1
    cfv
    cfv
    cE
    wcel
    @16
    @57
    ply1divmo.g3
    ad2antrr
    @72
    @75
    deg1mul2
    breqtrrd
    @17
    @19
    @63
    wceq
    @57
    @17
    @18
    @62
    cD
    @17
    @18
    @7
    @1
    c.mi
    co
    @62
    @17
    cB
    cP
    c.mi
    cF
    @1
    @7
    ply1divalg.b
    ply1divalg.m
    @17
    @34
    cP
    cabl
    wcel
    @37
    cP
    ringabl
    syl
    @41
    @45
    @49
    ablnnncan1
    @17
    cB
    cP
    c.xb
    c.mi
    cG
    @6
    @0
    ply1divalg.b
    ply1divalg.t
    ply1divalg.m
    @37
    @43
    @48
    @44
    ringsubdi
    eqtr4d
    fveq2d
    adantr
    breqtrrd
    @17
    @60
    @58
    wb
    #
    @57
    @17
    @26
    @22
    @76
    @56
    @51
    @4
    @19
    xrlenlt
    syl2anc
    adantr
    mpbid
    ex
    necon4ad
    syld
    ralrimivva
    @5
    @10
    vq
    vr
    cB
    @12
    @3
    @9
    @4
    clt
    @12
    @2
    @8
    cD
    @12
    @1
    @7
    cF
    c.mi
    @0
    @6
    cG
    c.xb
    oveq2
    oveq2d
    fveq2d
    breq1d
    rmo4
    sylibr
end
