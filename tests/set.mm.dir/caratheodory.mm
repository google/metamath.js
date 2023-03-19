include "cres.mm"
include "caragensal.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "omef.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "ccaragen.mm"
include "come.mm"
include "wcel.mm"
include "caragenval.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "fssresd.mm"
include "c0.mm"
include "caragen0.mm"
include "fvres.mm"
include "ome0.mm"
include "eqtrd.mm"
include "cn.mm"
include "wf.mm"
include "wdisj.mm"
include "w3a.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "simp1.mm"
include "simp2.mm"
include "fveq2.mm"
include "cbvdisjv.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "c1.mm"
include "cfz.mm"
include "3ad2ant1.mm"
include "biimpri.mm"
include "cbviunv.mm"
include "mpteq2i.mm"
include "caratheodorylem2.mm"
include "syl3anc.mm"
include "wa.mm"
include "csalg.mm"
include "adantr.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "nnenom.mm"
include "endom.mm"
include "ax-mp.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "saliuncl.mm"
include "3adant3.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "ismeannd.mm"

theorem caratheodory
  let wph: wff ph
  let cS: class S
  let cO: class O
  let va: setvar a
  let ve: setvar e
  let vj: setvar j
  let vn: setvar n
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume caratheodory.o: |- ( ph -> O e. OutMeas )
  assume caratheodory.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> ( O |` S ) e. Meas )

  proof
    wph
    cS
    ve
    vn
    cO
    cS
    cres
    #
    wph
    cS
    cO
    caratheodory.o
    caratheodory.s
    caragensal
    #
    wph
    cO
    cdm
    cuni
    #
    cpw
    #
    cc0
    cpnf
    cicc
    co
    cS
    cO
    wph
    cO
    @2
    caratheodory.o
    @2
    eqid
    #
    omef
    wph
    cS
    va
    cv
    #
    ve
    cv
    #
    cin
    cO
    cfv
    @5
    @6
    cdif
    cO
    cfv
    cxad
    co
    @5
    cO
    cfv
    wceq
    va
    @3
    wral
    #
    ve
    @3
    crab
    #
    @3
    wph
    @8
    cO
    ccaragen
    cfv
    #
    cS
    wph
    @9
    @8
    wph
    cO
    come
    wcel
    #
    @9
    @8
    wceq
    caratheodory.o
    ve
    cO
    va
    caragenval
    syl
    eqcomd
    @9
    cS
    wceq
    wph
    cS
    @9
    caratheodory.s
    eqcomi
    a1i
    eqtr2d
    @7
    ve
    @3
    ssrab2
    syl6eqss
    fssresd
    wph
    c0
    @0
    cfv
    #
    c0
    cO
    cfv
    #
    cc0
    wph
    c0
    cS
    wcel
    @11
    @12
    wceq
    wph
    cS
    cO
    caratheodory.o
    caratheodory.s
    caragen0
    c0
    cS
    cO
    fvres
    syl
    wph
    cO
    caratheodory.o
    ome0
    eqtrd
    wph
    cn
    cS
    @6
    wf
    #
    vn
    cn
    vn
    cv
    #
    @6
    cfv
    #
    wdisj
    #
    w3a
    #
    vn
    cn
    @15
    ciun
    #
    cO
    cfv
    #
    vn
    cn
    @15
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @18
    @0
    cfv
    #
    vn
    cn
    @15
    @0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @17
    wph
    @13
    vm
    cn
    vm
    cv
    #
    @6
    cfv
    #
    wdisj
    #
    @19
    @22
    wceq
    wph
    @13
    @16
    simp1
    wph
    @13
    @16
    simp2
    @16
    wph
    @29
    @13
    @16
    @29
    vn
    vm
    cn
    @15
    @28
    @14
    @27
    @6
    fveq2
    cbvdisjv
    #
    biimpi
    3ad2ant3
    wph
    @13
    @29
    w3a
    cS
    vj
    vn
    @6
    vj
    cn
    vm
    c1
    vj
    cv
    cfz
    co
    #
    @28
    ciun
    #
    cmpt
    cO
    @2
    wph
    @13
    @10
    @29
    caratheodory.o
    3ad2ant1
    @4
    caratheodory.s
    wph
    @13
    @29
    simp2
    @29
    wph
    @16
    @13
    @16
    @29
    @30
    biimpri
    3ad2ant3
    vj
    cn
    @32
    vn
    @31
    @15
    ciun
    vm
    vn
    @31
    @28
    @15
    @27
    @14
    @6
    fveq2
    cbviunv
    mpteq2i
    caratheodorylem2
    syl3anc
    wph
    @13
    @23
    @19
    wceq
    #
    @16
    wph
    @13
    wa
    #
    @18
    cS
    wcel
    @33
    @34
    cS
    vn
    @15
    cn
    wph
    cS
    csalg
    wcel
    @13
    @1
    adantr
    cn
    com
    cdom
    wbr
    #
    @34
    cn
    com
    cen
    wbr
    @35
    nnenom
    cn
    com
    endom
    ax-mp
    a1i
    @13
    @14
    cn
    wcel
    #
    @15
    cS
    wcel
    #
    wph
    cn
    cS
    @14
    @6
    ffvelrn
    adantll
    #
    saliuncl
    @18
    cS
    cO
    fvres
    syl
    3adant3
    wph
    @13
    @26
    @22
    wceq
    @16
    @34
    @25
    @21
    csumge0
    @34
    vn
    cn
    @24
    @20
    @34
    @36
    wa
    @37
    @24
    @20
    wceq
    @38
    @15
    cS
    cO
    fvres
    syl
    mpteq2dva
    fveq2d
    3adant3
    3eqtr4d
    ismeannd
end
