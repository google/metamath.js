include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "wrex.mm"
include "wcel.mm"
include "wsbc.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "sbceq2a.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "cfv.mm"
include "wsb.mm"
include "c1.mm"
include "cmin.mm"
include "sbsbc.mm"
include "nfv.mm"
include "sbhypf.mm"
include "syl5bbr.mm"
include "simprl.mm"
include "wfr.mm"
include "adantr.mm"
include "wo.mm"
include "nfsbc1v.mm"
include "nfcv.mm"
include "nfrex.mm"
include "nfor.mm"
include "nfim.mm"
include "sbceq1a.mm"
include "rexbidv.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "adantlr.mm"
include "wbr.mm"
include "nfan.mm"
include "anbi1d.mm"
include "breq2.mm"
include "adantllr.mm"
include "fdc.mm"
include "anassrs.mm"
include "idd.mm"
include "fvex.mm"
include "sbcie.mm"
include "dfsbcq.mm"
include "syl5rbbr.mm"
include "biimpcd.mm"
include "adantl.mm"
include "anim1d.mm"
include "3anim123d.mm"
include "eximdv.mm"
include "reximdv.mm"
include "mpd.mm"
include "chvarv.mm"
include "r19.29a.mm"

theorem fdc1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume fdc1.1: |- A e. _V
  assume fdc1.2: |- M e. ZZ
  assume fdc1.3: |- Z = ( ZZ>= ` M )
  assume fdc1.4: |- N = ( M + 1 )
  assume fdc1.5: |- ( a = ( f ` M ) -> ( ze <-> si ) )
  assume fdc1.6: |- ( a = ( f ` ( k - 1 ) ) -> ( ph <-> ps ) )
  assume fdc1.7: |- ( b = ( f ` k ) -> ( ps <-> ch ) )
  assume fdc1.8: |- ( a = ( f ` n ) -> ( th <-> ta ) )
  assume fdc1.9: |- ( et -> E. a e. A ze )
  assume fdc1.10: |- ( et -> R Fr A )
  assume fdc1.11: |- ( ( et /\ a e. A ) -> ( th \/ E. b e. A ph ) )
  assume fdc1.12: |- ( ( ( et /\ ph ) /\ ( a e. A /\ b e. A ) ) -> b R a )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A n
  disjoint a b
  disjoint a f
  disjoint a n
  disjoint b f
  disjoint b n
  disjoint f n
  disjoint R a
  disjoint R b
  disjoint M a
  disjoint M b
  disjoint M f
  disjoint M k
  disjoint M n
  disjoint a k
  disjoint b k
  disjoint f k
  disjoint k n
  disjoint Z a
  disjoint Z b
  disjoint Z n
  disjoint N a
  disjoint N b
  disjoint N f
  disjoint N k
  disjoint N n
  disjoint f ph
  disjoint k ph
  disjoint a ps
  disjoint a ch
  disjoint b ch
  disjoint ch n
  disjoint f th
  disjoint n th
  disjoint a ta
  disjoint b ta
  disjoint a et
  disjoint b et
  disjoint et f
  disjoint et n
  disjoint b ze
  disjoint f ze
  disjoint n ze
  disjoint a si
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c f
  disjoint c n
  disjoint d f
  disjoint d n
  disjoint R d
  disjoint M c
  disjoint M d
  disjoint c k
  disjoint d k
  disjoint Z c
  disjoint Z d
  disjoint N c
  disjoint N d
  disjoint d ph
  disjoint d ps
  disjoint c ch
  disjoint ch d
  disjoint d th
  disjoint c ta
  disjoint d ta
  disjoint c et
  disjoint d et
  disjoint c ze
  disjoint d ze
  disjoint c si
  assert |- ( et -> E. n e. Z E. f ( f : ( M ... n ) --> A /\ ( si /\ ta ) /\ A. k e. ( N ... n ) ch ) )

  proof
    wet
    wze
    cM
    vn
    cv
    #
    cfz
    co
    cA
    vf
    cv
    #
    wf
    #
    wsi
    wta
    wa
    #
    wch
    vk
    cN
    @0
    cfz
    co
    wral
    #
    w3a
    #
    vf
    wex
    #
    vn
    cZ
    wrex
    #
    va
    cA
    wet
    vc
    cv
    #
    cA
    wcel
    #
    wa
    #
    wze
    va
    @8
    wsbc
    #
    wa
    #
    @7
    wi
    wet
    va
    cv
    #
    cA
    wcel
    #
    wa
    #
    wze
    wa
    #
    @7
    wi
    vc
    va
    @8
    @13
    wceq
    #
    @12
    @16
    @7
    @17
    @10
    @15
    @11
    wze
    @17
    @9
    @14
    wet
    @8
    @13
    cA
    eleq1
    anbi2d
    wze
    va
    @8
    sbceq2a
    anbi12d
    imbi1d
    @12
    @2
    cM
    @1
    cfv
    #
    @8
    wceq
    #
    wta
    wa
    #
    @4
    w3a
    #
    vf
    wex
    #
    vn
    cZ
    wrex
    #
    @7
    wet
    @9
    @11
    @23
    wph
    va
    vd
    cv
    #
    wsbc
    #
    wps
    wch
    wth
    va
    @24
    wsbc
    #
    wta
    wet
    @9
    @11
    wa
    #
    wa
    cA
    @8
    cR
    vf
    vk
    vn
    cM
    cN
    cZ
    vd
    vb
    fdc1.1
    fdc1.2
    fdc1.3
    fdc1.4
    @25
    wph
    va
    vd
    wsb
    @24
    vk
    cv
    c1
    cmin
    co
    @1
    cfv
    #
    wceq
    wps
    wph
    va
    vd
    sbsbc
    wph
    wps
    va
    vd
    @28
    wps
    va
    nfv
    fdc1.6
    sbhypf
    syl5bbr
    fdc1.7
    @26
    wth
    va
    vd
    wsb
    @24
    @0
    @1
    cfv
    #
    wceq
    wta
    wth
    va
    vd
    sbsbc
    wth
    wta
    va
    vd
    @29
    wta
    va
    nfv
    fdc1.8
    sbhypf
    syl5bbr
    wet
    @9
    @11
    simprl
    wet
    cA
    cR
    wfr
    @27
    fdc1.10
    adantr
    wet
    @24
    cA
    wcel
    #
    @26
    @25
    vb
    cA
    wrex
    #
    wo
    #
    @27
    @15
    wth
    wph
    vb
    cA
    wrex
    #
    wo
    #
    wi
    wet
    @30
    wa
    #
    @32
    wi
    va
    vd
    @35
    @32
    va
    @35
    va
    nfv
    @26
    @31
    va
    wth
    va
    @24
    nfsbc1v
    @25
    va
    vb
    cA
    va
    cA
    nfcv
    wph
    va
    @24
    nfsbc1v
    #
    nfrex
    nfor
    nfim
    @13
    @24
    wceq
    #
    @15
    @35
    @34
    @32
    @37
    @14
    @30
    wet
    @13
    @24
    cA
    eleq1
    #
    anbi2d
    @37
    wth
    @26
    @33
    @31
    wth
    va
    @24
    sbceq1a
    @37
    wph
    @25
    vb
    cA
    wph
    va
    @24
    sbceq1a
    #
    rexbidv
    orbi12d
    imbi12d
    fdc1.11
    chvar
    adantlr
    wet
    @25
    @30
    vb
    cv
    #
    cA
    wcel
    #
    wa
    #
    @40
    @24
    cR
    wbr
    #
    @27
    wet
    wph
    wa
    #
    @14
    @41
    wa
    #
    wa
    #
    @40
    @13
    cR
    wbr
    #
    wi
    wet
    @25
    wa
    #
    @42
    wa
    #
    @43
    wi
    va
    vd
    @49
    @43
    va
    @48
    @42
    va
    wet
    @25
    va
    wet
    va
    nfv
    @36
    nfan
    @42
    va
    nfv
    nfan
    @43
    va
    nfv
    nfim
    @37
    @46
    @49
    @47
    @43
    @37
    @44
    @48
    @45
    @42
    @37
    wph
    @25
    wet
    @39
    anbi2d
    @37
    @14
    @30
    @41
    @38
    anbi1d
    anbi12d
    @13
    @24
    @40
    cR
    breq2
    imbi12d
    fdc1.12
    chvar
    adantllr
    fdc
    anassrs
    @12
    @22
    @6
    vn
    cZ
    @12
    @21
    @5
    vf
    @12
    @2
    @2
    @20
    @3
    @4
    @4
    @12
    @2
    idd
    @12
    @19
    wsi
    wta
    @11
    @19
    wsi
    wi
    @10
    @19
    @11
    wsi
    wsi
    wze
    va
    @18
    wsbc
    @19
    @11
    wze
    wsi
    va
    @18
    cM
    @1
    fvex
    fdc1.5
    sbcie
    wze
    va
    @18
    @8
    dfsbcq
    syl5rbbr
    biimpcd
    adantl
    anim1d
    @12
    @4
    idd
    3anim123d
    eximdv
    reximdv
    mpd
    chvarv
    fdc1.9
    r19.29a
end
