include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "cfn.mm"
include "wss.mm"
include "cmul.mm"
include "co.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "syl.mm"
include "cgcd.mm"
include "c1.mm"
include "csubg.mm"
include "cabl.mm"
include "cz.mm"
include "nnzd.mm"
include "oddvdssubg.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "lagsubg.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "ablfacrplem.mm"
include "wa.mm"
include "wi.mm"
include "nn0zd.mm"
include "coprmdvds.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "gcdcom.mm"
include "eqtr3d.mm"
include "dvdscmul.mm"
include "mpd.mm"
include "clsm.mm"
include "cin.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "ablfacrp.mm"
include "simprd.mm"
include "fveq2d.mm"
include "ccntz.mm"
include "simpld.mm"
include "ablcntzd.mm"
include "lsmhash.mm"
include "breqtrrd.mm"
include "cc0.mm"
include "wne.mm"
include "cn.mm"
include "c0.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "3syl.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnne0d.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "dvdsmulc.mm"
include "dvdscmulr.mm"
include "jca.mm"

theorem ablfacrp2
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
  assert |- ( ph -> ( ( # ` K ) = M /\ ( # ` L ) = N ) )

  proof
    wph
    cK
    chash
    cfv
    #
    cM
    wceq
    #
    cL
    chash
    cfv
    #
    cN
    wceq
    #
    wph
    @0
    cn0
    wcel
    #
    cM
    cn0
    wcel
    @0
    cM
    cdvds
    wbr
    #
    cM
    @0
    cdvds
    wbr
    #
    @1
    wph
    cK
    cfn
    wcel
    #
    @4
    wph
    cB
    cfn
    wcel
    #
    cK
    cB
    wss
    @7
    wph
    cB
    chash
    cfv
    #
    cn0
    wcel
    #
    @8
    wph
    @9
    cM
    cN
    cmul
    co
    #
    cn0
    ablfacrp.2
    wph
    cM
    cN
    wph
    cM
    ablfacrp.m
    nnnn0d
    #
    wph
    cN
    ablfacrp.n
    nnnn0d
    #
    nn0mulcld
    eqeltrd
    cB
    cvv
    wcel
    @8
    @10
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
    #
    cK
    vx
    cv
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
    cB
    ablfacrp.k
    @16
    vx
    cB
    ssrab2
    eqsstri
    cB
    cK
    ssfi
    sylancl
    #
    cK
    hashcl
    syl
    #
    @12
    wph
    @0
    cN
    cM
    cmul
    co
    #
    cdvds
    wbr
    #
    @0
    cN
    cgcd
    co
    c1
    wceq
    #
    @5
    wph
    @0
    @9
    @20
    cdvds
    wph
    cK
    cG
    csubg
    cfv
    #
    wcel
    @8
    @0
    @9
    cdvds
    wbr
    wph
    cK
    @17
    @23
    ablfacrp.k
    wph
    cG
    cabl
    wcel
    #
    cM
    cz
    wcel
    #
    @17
    @23
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
    #
    @14
    cG
    cB
    cK
    ablfacrp.b
    lagsubg
    syl2anc
    wph
    @9
    @11
    @20
    ablfacrp.2
    wph
    cM
    cN
    wph
    cM
    ablfacrp.m
    nncnd
    wph
    cN
    ablfacrp.n
    nncnd
    mulcomd
    eqtrd
    #
    breqtrd
    wph
    vx
    cB
    cG
    cK
    cL
    cM
    cN
    cO
    ablfacrp.b
    ablfacrp.o
    ablfacrp.k
    ablfacrp.l
    ablfacrp.g
    ablfacrp.m
    ablfacrp.n
    ablfacrp.1
    ablfacrp.2
    ablfacrplem
    wph
    @0
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @25
    @21
    @22
    wa
    @5
    wi
    wph
    @0
    @19
    nn0zd
    #
    wph
    cN
    ablfacrp.n
    nnzd
    #
    @26
    @0
    cN
    cM
    coprmdvds
    syl3anc
    mp2and
    #
    wph
    cM
    @2
    cmul
    co
    #
    @0
    @2
    cmul
    co
    #
    cdvds
    wbr
    #
    @6
    wph
    @34
    @11
    @35
    cdvds
    wph
    @2
    cN
    cdvds
    wbr
    #
    @34
    @11
    cdvds
    wbr
    #
    wph
    @2
    @11
    cdvds
    wbr
    #
    @2
    cM
    cgcd
    co
    c1
    wceq
    #
    @37
    wph
    @2
    @9
    @11
    cdvds
    wph
    cL
    @23
    wcel
    #
    @8
    @2
    @9
    cdvds
    wbr
    wph
    cL
    @15
    cN
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    @23
    ablfacrp.l
    wph
    @24
    @30
    @43
    @23
    wcel
    ablfacrp.g
    @32
    vx
    cB
    cG
    cN
    cO
    ablfacrp.o
    ablfacrp.b
    oddvdssubg
    syl2anc
    syl5eqel
    #
    @14
    cG
    cB
    cL
    ablfacrp.b
    lagsubg
    syl2anc
    ablfacrp.2
    breqtrd
    wph
    vx
    cB
    cG
    cL
    cK
    cN
    cM
    cO
    ablfacrp.b
    ablfacrp.o
    ablfacrp.l
    ablfacrp.k
    ablfacrp.g
    ablfacrp.n
    ablfacrp.m
    wph
    cM
    cN
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    #
    c1
    wph
    @25
    @30
    @45
    @46
    wceq
    @26
    @32
    cM
    cN
    gcdcom
    syl2anc
    ablfacrp.1
    eqtr3d
    @28
    ablfacrplem
    wph
    @2
    cz
    wcel
    #
    @25
    @30
    @39
    @40
    wa
    @37
    wi
    wph
    @2
    wph
    cL
    cfn
    wcel
    #
    @2
    cn0
    wcel
    #
    wph
    @8
    cL
    cB
    wss
    @48
    @14
    cL
    @43
    cB
    ablfacrp.l
    @42
    vx
    cB
    ssrab2
    eqsstri
    cB
    cL
    ssfi
    sylancl
    #
    cL
    hashcl
    syl
    #
    nn0zd
    #
    @26
    @32
    @2
    cM
    cN
    coprmdvds
    syl3anc
    mp2and
    #
    wph
    @47
    @30
    @25
    @37
    @38
    wi
    @52
    @32
    @26
    cM
    @2
    cN
    dvdscmul
    syl3anc
    mpd
    wph
    @9
    @35
    @11
    wph
    cK
    cL
    cG
    clsm
    cfv
    #
    co
    #
    chash
    cfv
    @9
    @35
    wph
    @55
    cB
    chash
    wph
    cK
    cL
    cin
    cG
    c0g
    cfv
    #
    csn
    wceq
    #
    @55
    cB
    wceq
    #
    wph
    vx
    cB
    @54
    cG
    cK
    cL
    cM
    cN
    cO
    @56
    ablfacrp.b
    ablfacrp.o
    ablfacrp.k
    ablfacrp.l
    ablfacrp.g
    ablfacrp.m
    ablfacrp.n
    ablfacrp.1
    ablfacrp.2
    @56
    eqid
    #
    @54
    eqid
    #
    ablfacrp
    #
    simprd
    fveq2d
    wph
    @54
    cK
    cL
    cG
    @56
    cG
    ccntz
    cfv
    #
    @60
    @59
    @62
    eqid
    #
    @27
    @44
    wph
    @57
    @58
    @61
    simpld
    wph
    cK
    cL
    cG
    @62
    @63
    ablfacrp.g
    @27
    @44
    ablcntzd
    @18
    @50
    lsmhash
    eqtr3d
    ablfacrp.2
    eqtr3d
    #
    breqtrrd
    wph
    @25
    @29
    @47
    @2
    cc0
    wne
    @36
    @6
    wb
    @26
    @31
    @52
    wph
    @2
    wph
    @2
    cn
    wcel
    #
    cL
    c0
    wne
    #
    wph
    @41
    @56
    cL
    wcel
    @66
    @44
    cL
    cG
    @56
    @59
    subg0cl
    cL
    @56
    ne0i
    3syl
    wph
    @48
    @65
    @66
    wb
    @50
    cL
    hashnncl
    syl
    mpbird
    nnne0d
    @2
    cM
    @0
    dvdsmulcr
    syl112anc
    mpbid
    @0
    cM
    dvdseq
    syl22anc
    #
    wph
    @49
    cN
    cn0
    wcel
    @37
    cN
    @2
    cdvds
    wbr
    #
    @3
    @51
    @13
    @53
    wph
    @0
    cN
    cmul
    co
    #
    @35
    cdvds
    wbr
    #
    @68
    wph
    @69
    @11
    @35
    cdvds
    wph
    @5
    @69
    @11
    cdvds
    wbr
    #
    @33
    wph
    @29
    @25
    @30
    @5
    @71
    wi
    @31
    @26
    @32
    cN
    @0
    cM
    dvdsmulc
    syl3anc
    mpd
    @64
    breqtrrd
    wph
    @30
    @47
    @29
    @0
    cc0
    wne
    @70
    @68
    wb
    @32
    @52
    @31
    wph
    @0
    wph
    @0
    cM
    cn
    @67
    ablfacrp.m
    eqeltrd
    nnne0d
    @0
    cN
    @2
    dvdscmulr
    syl112anc
    mpbid
    @2
    cN
    dvdseq
    syl22anc
    jca
end
