include "chash.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "wn.mm"
include "nprmdvds1.mm"
include "adantl.mm"
include "adantr.mm"
include "breq2d.mm"
include "mtbird.mm"
include "cress.mm"
include "cod.mm"
include "cbs.mm"
include "cgrp.mm"
include "cfn.mm"
include "csubg.mm"
include "crab.mm"
include "cabl.mm"
include "cz.mm"
include "nnzd.mm"
include "oddvdssubg.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "subggrp.mm"
include "syl.mm"
include "subgbas.mm"
include "wss.mm"
include "cn0.mm"
include "cmul.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "simplr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "odcau.mm"
include "syl31anc.mm"
include "rexeqdv.mm"
include "mpbird.mm"
include "subgod.mm"
include "sylan.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "eqbrtrrd.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "anim1d.mm"
include "prmz.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "dvdsgcdb.mm"
include "syl3anc.mm"
include "3imtr3d.mm"
include "mtod.mm"
include "nrexdv.mm"
include "exprmfct.mm"
include "nsyl.mm"
include "cn.mm"
include "wo.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0d.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"

theorem ablfacrplem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  let c.po: class .(+)
  let c.0: class .0.
  assume ablfacrp.b: |- B = ( Base ` G )
  assume ablfacrp.o: |- O = ( od ` G )
  assume ablfacrp.k: |- K = { x e. B | ( O ` x ) || M }
  assume ablfacrp.l: |- L = { x e. B | ( O ` x ) || N }
  assume ablfacrp.g: |- ( ph -> G e. Abel )
  assume ablfacrp.m: |- ( ph -> M e. NN )
  assume ablfacrp.n: |- ( ph -> N e. NN )
  assume ablfacrp.1: |- ( ph -> ( M gcd N ) = 1 )
  assume ablfacrp.2: |- ( ph -> ( # ` B ) = ( M x. N ) )

  disjoint B x
  disjoint G x
  disjoint O x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint a b
  disjoint a g
  disjoint a x
  disjoint B a
  disjoint b g
  disjoint b x
  disjoint B b
  disjoint g x
  disjoint B g
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint a p
  disjoint K a
  disjoint b p
  disjoint K b
  disjoint g p
  disjoint K g
  disjoint K p
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) g
  disjoint M a
  disjoint M b
  disjoint M g
  disjoint N a
  disjoint N b
  disjoint p x
  disjoint N p
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint p ph
  disjoint .0. x
  assert |- ( ph -> ( ( # ` K ) gcd N ) = 1 )

  proof
    wph
    cK
    chash
    cfv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @1
    c2
    cuz
    cfv
    wcel
    #
    wph
    vp
    cv
    #
    @1
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    @3
    wph
    @5
    vp
    cprime
    wph
    @4
    cprime
    wcel
    #
    wa
    #
    @5
    @4
    cM
    cN
    cgcd
    co
    #
    cdvds
    wbr
    #
    @7
    @9
    @4
    c1
    cdvds
    wbr
    #
    @6
    @10
    wn
    wph
    @4
    nprmdvds1
    adantl
    @7
    @8
    c1
    @4
    cdvds
    wph
    @8
    c1
    wceq
    @6
    ablfacrp.1
    adantr
    breq2d
    mtbird
    @7
    @4
    @0
    cdvds
    wbr
    #
    @4
    cN
    cdvds
    wbr
    #
    wa
    #
    @4
    cM
    cdvds
    wbr
    #
    @12
    wa
    #
    @5
    @9
    @7
    @11
    @14
    @12
    @7
    @11
    @14
    @7
    @11
    wa
    #
    vg
    cv
    #
    cG
    cK
    cress
    co
    #
    cod
    cfv
    #
    cfv
    #
    @4
    wceq
    #
    vg
    cK
    wrex
    #
    @14
    @16
    @22
    @21
    vg
    @18
    cbs
    cfv
    #
    wrex
    #
    @16
    @18
    cgrp
    wcel
    #
    @23
    cfn
    wcel
    @6
    @4
    @23
    chash
    cfv
    #
    cdvds
    wbr
    @24
    @16
    cK
    cG
    csubg
    cfv
    #
    wcel
    #
    @25
    wph
    @28
    @6
    @11
    wph
    cK
    vx
    cv
    #
    cO
    cfv
    #
    cM
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    @27
    ablfacrp.k
    wph
    cG
    cabl
    wcel
    cM
    cz
    wcel
    #
    @32
    @27
    wcel
    ablfacrp.g
    wph
    cM
    ablfacrp.m
    nnzd
    #
    vx
    cB
    cG
    cM
    cO
    ablfacrp.o
    ablfacrp.b
    oddvdssubg
    syl2anc
    syl5eqel
    ad2antrr
    #
    cK
    cG
    @18
    @18
    eqid
    #
    subggrp
    syl
    @16
    cK
    @23
    cfn
    @16
    @28
    cK
    @23
    wceq
    @35
    cK
    cG
    @18
    @36
    subgbas
    syl
    #
    wph
    cK
    cfn
    wcel
    #
    @6
    @11
    wph
    cB
    cfn
    wcel
    #
    cK
    cB
    wss
    @38
    wph
    cB
    chash
    cfv
    #
    cn0
    wcel
    #
    @39
    wph
    @40
    cM
    cN
    cmul
    co
    cn0
    ablfacrp.2
    wph
    cM
    cN
    wph
    cM
    ablfacrp.m
    nnnn0d
    wph
    cN
    ablfacrp.n
    nnnn0d
    nn0mulcld
    eqeltrd
    cB
    cvv
    wcel
    @39
    @41
    wb
    cB
    cG
    cbs
    cfv
    cvv
    ablfacrp.b
    cG
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashclb
    ax-mp
    sylibr
    cK
    @32
    cB
    ablfacrp.k
    @31
    vx
    cB
    ssrab2
    eqsstri
    cB
    cK
    ssfi
    sylancl
    #
    ad2antrr
    eqeltrrd
    wph
    @6
    @11
    simplr
    @16
    @4
    @0
    @26
    cdvds
    @7
    @11
    simpr
    @16
    cK
    @23
    chash
    @37
    fveq2d
    breqtrd
    @4
    vg
    @18
    @19
    @23
    @23
    eqid
    @19
    eqid
    #
    odcau
    syl31anc
    @16
    @21
    vg
    cK
    @23
    @37
    rexeqdv
    mpbird
    @16
    @21
    @14
    vg
    cK
    @16
    @17
    cK
    wcel
    #
    wa
    #
    @20
    cM
    cdvds
    wbr
    @21
    @14
    @45
    @17
    cO
    cfv
    #
    @20
    cM
    cdvds
    @16
    @28
    @44
    @46
    @20
    wceq
    @35
    @17
    @19
    cG
    @18
    cO
    cK
    @36
    ablfacrp.o
    @43
    subgod
    sylan
    @44
    @46
    cM
    cdvds
    wbr
    #
    @16
    @44
    @17
    cB
    wcel
    @47
    @31
    @47
    vx
    @17
    cB
    cK
    @29
    @17
    wceq
    @30
    @46
    cM
    cdvds
    @29
    @17
    cO
    fveq2
    breq1d
    ablfacrp.k
    elrab2
    simprbi
    adantl
    eqbrtrrd
    @20
    @4
    cM
    cdvds
    breq1
    syl5ibcom
    rexlimdva
    mpd
    ex
    anim1d
    @7
    @4
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @13
    @5
    wb
    @6
    @48
    wph
    @4
    prmz
    adantl
    #
    wph
    @49
    @6
    wph
    @0
    wph
    @38
    @0
    cn0
    wcel
    @42
    cK
    hashcl
    syl
    nn0zd
    #
    adantr
    wph
    @50
    @6
    wph
    cN
    ablfacrp.n
    nnzd
    #
    adantr
    #
    @4
    @0
    cN
    dvdsgcdb
    syl3anc
    @7
    @48
    @33
    @50
    @15
    @9
    wb
    @51
    wph
    @33
    @6
    @34
    adantr
    @54
    @4
    cM
    cN
    dvdsgcdb
    syl3anc
    3imtr3d
    mtod
    nrexdv
    @1
    vp
    exprmfct
    nsyl
    wph
    @2
    @3
    wph
    @1
    cn
    wcel
    #
    @2
    @3
    wo
    wph
    @49
    @50
    @0
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @55
    @52
    @53
    wph
    cN
    cc0
    wne
    @59
    wph
    cN
    ablfacrp.n
    nnne0d
    @58
    cN
    cc0
    @56
    @57
    simpr
    necon3ai
    syl
    @0
    cN
    gcdn0cl
    syl21anc
    @1
    elnn1uz2
    sylib
    ord
    mt3d
end
