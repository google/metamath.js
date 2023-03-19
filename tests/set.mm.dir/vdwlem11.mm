include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "cvdwm.mm"
include "wbr.mm"
include "cfz.mm"
include "cmap.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "chash.mm"
include "cfv.mm"
include "cop.mm"
include "cvdwp.mm"
include "wo.mm"
include "cn0.mm"
include "wcel.mm"
include "cfn.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0p1nn.mm"
include "vdwlem10.mm"
include "wa.mm"
include "wf.mm"
include "wb.mm"
include "cvv.mm"
include "adantr.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "wn.mm"
include "cle.mm"
include "clt.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "cr.mm"
include "peano2re.mm"
include "ltnled.mm"
include "mpbid.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "eluz2nn.mm"
include "nnnn0d.mm"
include "simprr.mm"
include "eqid.mm"
include "vdwpc.mm"
include "cdom.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "simpr.mm"
include "cnvimass.mm"
include "syl6ss.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "simplrl.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "ffvelrnda.mm"
include "nnaddcld.mm"
include "vdwapid1.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "ex.mm"
include "ffvelrn.mm"
include "syl6an.mm"
include "ralimdva.mm"
include "imp.mm"
include "fmpt.mm"
include "frn.mm"
include "ssdomg.mm"
include "sylc.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashdom.mm"
include "mpbird.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "mtod.mm"
include "biorf.mm"
include "anassrs.mm"
include "syldan.mm"
include "ralbidva.mm"
include "rexbidva.mm"

theorem vdwlem11
  let wph: wff ph
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  let vs: setvar s
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W
  let cF: class F
  let vr: setvar r
  let cM: class M
  let cH: class H
  assume vdw.r: |- ( ph -> R e. Fin )
  assume vdwlem9.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem9.s: |- ( ph -> A. s e. Fin E. n e. NN A. f e. ( s ^m ( 1 ... n ) ) K MonoAP f )

  disjoint f ph
  disjoint n ph
  disjoint f n
  disjoint f s
  disjoint K f
  disjoint n s
  disjoint K n
  disjoint K s
  disjoint R f
  disjoint R n
  disjoint R s
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint c d
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c ph
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint d ph
  disjoint g h
  disjoint g i
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g ph
  disjoint h i
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint h ph
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint k ph
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint m ph
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W f
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint a f
  disjoint F a
  disjoint c f
  disjoint F c
  disjoint d f
  disjoint F d
  disjoint f g
  disjoint f w
  disjoint F f
  disjoint F g
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a r
  disjoint a s
  disjoint K a
  disjoint c r
  disjoint c s
  disjoint K c
  disjoint d r
  disjoint d s
  disjoint K d
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint g r
  disjoint g s
  disjoint K g
  disjoint h r
  disjoint h s
  disjoint K h
  disjoint i r
  disjoint i s
  disjoint K i
  disjoint k r
  disjoint k s
  disjoint K k
  disjoint m r
  disjoint m s
  disjoint K m
  disjoint n r
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint K r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M a
  disjoint M d
  disjoint M f
  disjoint M g
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R r
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint H a
  disjoint H d
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint H z
  assert |- ( ph -> E. n e. NN A. f e. ( R ^m ( 1 ... n ) ) ( K + 1 ) MonoAP f )

  proof
    wph
    cK
    c1
    caddc
    co
    vf
    cv
    #
    cvdwm
    wbr
    #
    vf
    cR
    c1
    vn
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    cR
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cK
    cop
    @0
    cvdwp
    wbr
    #
    @1
    wo
    #
    vf
    @4
    wral
    #
    vn
    cn
    wrex
    wph
    cR
    vf
    vn
    cK
    @7
    vs
    vdw.r
    vdwlem9.k
    vdwlem9.s
    wph
    @6
    cn0
    wcel
    #
    @7
    cn
    wcel
    #
    wph
    cR
    cfn
    wcel
    #
    @11
    vdw.r
    cR
    hashcl
    syl
    #
    @6
    nn0p1nn
    syl
    #
    vdwlem10
    wph
    @5
    @10
    vn
    cn
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @1
    @9
    vf
    @4
    @17
    @0
    @4
    wcel
    #
    @3
    cR
    @0
    wf
    #
    @1
    @9
    wb
    #
    @17
    @18
    @19
    @17
    @13
    @3
    cvv
    wcel
    @18
    @19
    wb
    wph
    @13
    @16
    vdw.r
    adantr
    c1
    @2
    cfz
    ovex
    #
    cR
    @3
    @0
    cfn
    cvv
    elmapg
    sylancl
    biimpa
    wph
    @16
    @19
    @20
    wph
    @16
    @19
    wa
    #
    wa
    #
    @8
    wn
    @20
    @23
    @8
    @7
    @6
    cle
    wbr
    #
    wph
    @24
    wn
    #
    @22
    wph
    @6
    @7
    clt
    wbr
    @25
    wph
    @6
    wph
    @6
    @14
    nn0red
    #
    ltp1d
    wph
    @6
    @7
    @26
    wph
    @6
    cr
    wcel
    @7
    cr
    wcel
    @26
    @6
    peano2re
    syl
    ltnled
    mpbid
    adantr
    @23
    @8
    va
    cv
    #
    vi
    cv
    #
    vd
    cv
    #
    cfv
    #
    caddc
    co
    #
    @30
    cK
    cvdwa
    cfv
    co
    #
    @0
    ccnv
    @31
    @0
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    c1
    @7
    cfz
    co
    #
    wral
    #
    vi
    @37
    @33
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    @7
    wceq
    #
    wa
    #
    vd
    cn
    @37
    cmap
    co
    #
    wrex
    va
    cn
    wrex
    @24
    @23
    cR
    vi
    @0
    @37
    cK
    @7
    @3
    va
    vd
    @21
    @23
    cK
    wph
    cK
    cn
    wcel
    #
    @22
    wph
    cK
    c2
    cuz
    cfv
    wcel
    @45
    vdwlem9.k
    cK
    eluz2nn
    syl
    #
    adantr
    nnnn0d
    wph
    @16
    @19
    simprr
    #
    wph
    @12
    @22
    @15
    adantr
    @37
    eqid
    vdwpc
    @23
    @43
    @24
    va
    vd
    cn
    @44
    @23
    @27
    cn
    wcel
    #
    @29
    @44
    wcel
    #
    wa
    #
    wa
    #
    @38
    @42
    @24
    @51
    @38
    wa
    #
    @41
    @6
    cle
    wbr
    #
    @42
    @24
    @52
    @53
    @40
    cR
    cdom
    wbr
    #
    @52
    @13
    @40
    cR
    wss
    #
    @54
    wph
    @13
    @22
    @50
    @38
    vdw.r
    ad3antrrr
    #
    @52
    @37
    cR
    @39
    wf
    #
    @55
    @52
    @33
    cR
    wcel
    #
    vi
    @37
    wral
    #
    @57
    @51
    @38
    @59
    @51
    @36
    @58
    vi
    @37
    @51
    @28
    @37
    wcel
    #
    wa
    #
    @19
    @36
    @31
    @3
    wcel
    #
    @58
    @23
    @19
    @50
    @60
    @47
    ad2antrr
    @61
    @36
    @62
    @61
    @36
    wa
    #
    @32
    @3
    @31
    @63
    @32
    @0
    cdm
    #
    @3
    @63
    @32
    @35
    @64
    @61
    @36
    simpr
    @0
    @34
    cnvimass
    syl6ss
    @63
    @19
    @64
    @3
    wceq
    @23
    @19
    @50
    @60
    @36
    @47
    ad3antrrr
    @3
    cR
    @0
    fdm
    syl
    sseqtrd
    @61
    @31
    @32
    wcel
    #
    @36
    @61
    @45
    @31
    cn
    wcel
    @30
    cn
    wcel
    @65
    wph
    @45
    @22
    @50
    @60
    @46
    ad3antrrr
    @61
    @27
    @30
    @23
    @48
    @49
    @60
    simplrl
    @51
    @37
    cn
    @28
    @29
    @51
    @49
    @37
    cn
    @29
    wf
    @23
    @48
    @49
    simprr
    cn
    @37
    @29
    nnex
    c1
    @7
    cfz
    ovex
    elmap
    sylib
    ffvelrnda
    #
    nnaddcld
    @66
    @31
    @30
    cK
    vdwapid1
    syl3anc
    adantr
    sseldd
    ex
    @3
    cR
    @31
    @0
    ffvelrn
    syl6an
    ralimdva
    imp
    vi
    @37
    cR
    @33
    @39
    @39
    eqid
    fmpt
    sylib
    @37
    cR
    @39
    frn
    syl
    #
    @40
    cR
    cfn
    ssdomg
    sylc
    @52
    @40
    cfn
    wcel
    #
    @13
    @53
    @54
    wb
    @52
    @13
    @55
    @68
    @56
    @67
    cR
    @40
    ssfi
    syl2anc
    @56
    @40
    cR
    cfn
    hashdom
    syl2anc
    mpbird
    @41
    @7
    @6
    cle
    breq1
    syl5ibcom
    expimpd
    rexlimdvva
    sylbid
    mtod
    @8
    @1
    biorf
    syl
    anassrs
    syldan
    ralbidva
    rexbidva
    mpbird
end
