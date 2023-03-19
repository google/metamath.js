include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "caddc.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "csn.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "iuneq1.mm"
include "1ex.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "a1i.mm"
include "wa.mm"
include "cun.mm"
include "simpll.mm"
include "cuz.mm"
include "elnnuz.mm"
include "fzsuc.mm"
include "sylbi.mm"
include "iunxun.mm"
include "ovex.mm"
include "uneq2i.mm"
include "syl6eq.mm"
include "syl.mm"
include "simpr.mm"
include "uneq1d.mm"
include "simplr.mm"
include "wss.mm"
include "wsb.mm"
include "sbt.mm"
include "sbim.mm"
include "sban.mm"
include "nfv.mm"
include "sbf.mm"
include "clelsb3.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "wsbc.mm"
include "csb.mm"
include "sbsbc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcssg.mm"
include "csbfv.mm"
include "csbfv2g.mm"
include "csbov1g.mm"
include "fveq2i.mm"
include "csbvarg.mm"
include "oveq1i.mm"
include "3eqtri.mm"
include "sseq12i.mm"
include "3bitrri.mm"
include "imbi12i.mm"
include "bitr4i.mm"
include "mpbi.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem iuninc
  let wph: wff ph
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  assume iuninc.1: |- ( ph -> F Fn NN )
  assume iuninc.2: |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) )

  disjoint i n
  disjoint F n
  disjoint n ph
  disjoint i j
  disjoint j n
  disjoint j k
  disjoint F j
  disjoint k n
  disjoint F k
  disjoint j ph
  disjoint k ph
  assert |- ( ( ph /\ i e. NN ) -> U_ n e. ( 1 ... i ) ( F ` n ) = ( F ` i ) )

  proof
    vi
    cv
    #
    cn
    wcel
    wph
    vn
    c1
    @0
    cfz
    co
    #
    vn
    cv
    #
    cF
    cfv
    #
    ciun
    #
    @0
    cF
    cfv
    #
    wceq
    #
    wph
    vn
    c1
    vj
    cv
    #
    cfz
    co
    #
    @3
    ciun
    #
    @7
    cF
    cfv
    #
    wceq
    #
    wi
    wph
    vn
    c1
    c1
    cfz
    co
    #
    @3
    ciun
    #
    c1
    cF
    cfv
    #
    wceq
    #
    wi
    wph
    vn
    c1
    vk
    cv
    #
    cfz
    co
    #
    @3
    ciun
    #
    @16
    cF
    cfv
    #
    wceq
    #
    wi
    wph
    vn
    c1
    @16
    c1
    caddc
    co
    #
    cfz
    co
    #
    @3
    ciun
    #
    @21
    cF
    cfv
    #
    wceq
    #
    wi
    wph
    @6
    wi
    vj
    vk
    @0
    @7
    c1
    wceq
    #
    @11
    @15
    wph
    @26
    @9
    @13
    @10
    @14
    @26
    vn
    @8
    @12
    @3
    @7
    c1
    c1
    cfz
    oveq2
    iuneq1d
    @7
    c1
    cF
    fveq2
    eqeq12d
    imbi2d
    @7
    @16
    wceq
    #
    @11
    @20
    wph
    @27
    @9
    @18
    @10
    @19
    @27
    vn
    @8
    @17
    @3
    @7
    @16
    c1
    cfz
    oveq2
    iuneq1d
    @7
    @16
    cF
    fveq2
    eqeq12d
    imbi2d
    @7
    @21
    wceq
    #
    @11
    @25
    wph
    @28
    @9
    @23
    @10
    @24
    @28
    vn
    @8
    @22
    @3
    @7
    @21
    c1
    cfz
    oveq2
    iuneq1d
    @7
    @21
    cF
    fveq2
    eqeq12d
    imbi2d
    @7
    @0
    wceq
    #
    @11
    @6
    wph
    @29
    @9
    @4
    @10
    @5
    @29
    vn
    @8
    @1
    @3
    @7
    @0
    c1
    cfz
    oveq2
    iuneq1d
    @7
    @0
    cF
    fveq2
    eqeq12d
    imbi2d
    @15
    wph
    @13
    vn
    c1
    csn
    #
    @3
    ciun
    #
    @14
    @12
    @30
    wceq
    #
    @13
    @31
    wceq
    c1
    cz
    wcel
    @32
    1z
    c1
    fzsn
    ax-mp
    vn
    @12
    @30
    @3
    iuneq1
    ax-mp
    vn
    c1
    @3
    @14
    1ex
    @2
    c1
    cF
    fveq2
    iunxsn
    eqtri
    a1i
    @16
    cn
    wcel
    #
    wph
    @20
    @25
    @33
    wph
    @20
    @25
    @33
    wph
    wa
    #
    @20
    wa
    #
    @23
    @18
    @24
    cun
    #
    @19
    @24
    cun
    #
    @24
    @35
    @33
    @23
    @36
    wceq
    @33
    wph
    @20
    simpll
    #
    @33
    @23
    vn
    @17
    @21
    csn
    #
    cun
    #
    @3
    ciun
    #
    @36
    @33
    vn
    @22
    @40
    @3
    @33
    @16
    c1
    cuz
    cfv
    wcel
    @22
    @40
    wceq
    @16
    elnnuz
    c1
    @16
    fzsuc
    sylbi
    iuneq1d
    @41
    @18
    vn
    @39
    @3
    ciun
    #
    cun
    @36
    vn
    @17
    @39
    @3
    iunxun
    @42
    @24
    @18
    vn
    @21
    @3
    @24
    @16
    c1
    caddc
    ovex
    @2
    @21
    cF
    fveq2
    iunxsn
    uneq2i
    eqtri
    syl6eq
    syl
    @35
    @18
    @19
    @24
    @34
    @20
    simpr
    uneq1d
    @35
    wph
    @33
    @37
    @24
    wceq
    #
    @33
    wph
    @20
    simplr
    @38
    wph
    @33
    wa
    #
    @19
    @24
    wss
    #
    @43
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @3
    @2
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    wi
    #
    vn
    vk
    wsb
    #
    @44
    @45
    wi
    #
    @51
    vn
    vk
    iuninc.2
    sbt
    @52
    @47
    vn
    vk
    wsb
    #
    @50
    vn
    vk
    wsb
    #
    wi
    @53
    @47
    @50
    vn
    vk
    sbim
    @44
    @54
    @45
    @55
    @54
    wph
    vn
    vk
    wsb
    #
    @46
    vn
    vk
    wsb
    #
    wa
    @44
    wph
    @46
    vn
    vk
    sban
    @56
    wph
    @57
    @33
    wph
    vn
    vk
    wph
    vn
    nfv
    sbf
    vk
    vn
    cn
    clelsb3
    anbi12i
    bitr2i
    @55
    @50
    vn
    @16
    wsbc
    #
    vn
    @16
    @3
    csb
    #
    vn
    @16
    @49
    csb
    #
    wss
    #
    @45
    @50
    vn
    vk
    sbsbc
    @16
    cvv
    wcel
    #
    @58
    @61
    wb
    vk
    vex
    #
    vn
    @16
    @3
    @49
    cvv
    sbcssg
    ax-mp
    @59
    @19
    @60
    @24
    vn
    @16
    cF
    csbfv
    @60
    vn
    @16
    @48
    csb
    #
    cF
    cfv
    #
    vn
    @16
    @2
    csb
    #
    c1
    caddc
    co
    #
    cF
    cfv
    @24
    @62
    @60
    @65
    wceq
    @63
    vn
    @16
    @48
    cvv
    cF
    csbfv2g
    ax-mp
    @64
    @67
    cF
    @62
    @64
    @67
    wceq
    @63
    vn
    @16
    @2
    c1
    caddc
    cvv
    csbov1g
    ax-mp
    fveq2i
    @67
    @21
    cF
    @66
    @16
    c1
    caddc
    @62
    @66
    @16
    wceq
    @63
    vn
    @16
    cvv
    csbvarg
    ax-mp
    oveq1i
    fveq2i
    3eqtri
    sseq12i
    3bitrri
    imbi12i
    bitr4i
    mpbi
    @19
    @24
    ssequn1
    sylib
    syl2anc
    3eqtrd
    exp31
    a2d
    nnind
    impcom
end
