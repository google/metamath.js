include "cgsu.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "wceq.mm"
include "cseq.mm"
include "cfv.mm"
include "wa.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "crn.mm"
include "wss.mm"
include "c0g.mm"
include "wcel.mm"
include "c1.mm"
include "ccnv.mm"
include "cvv.mm"
include "cdif.mm"
include "cima.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "eqid.mm"
include "eqidd.mm"
include "ovexd.mm"
include "gsumval.mm"
include "iffalsed.mm"
include "cz.mm"
include "eluzel2.mm"
include "syl.mm"
include "eluzelz.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "fzf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnovrn.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "fvex.mm"
include "wb.mm"
include "wi.mm"
include "fzopth.mm"
include "simpl.mm"
include "seqeq1d.mm"
include "simpr.mm"
include "fveq12d.mm"
include "eqcomd.mm"
include "eqeq1.mm"
include "syl5ibrcom.mm"
include "syl6bi.mm"
include "impd.mm"
include "rexlimdvw.mm"
include "exlimdv.mm"
include "adantr.mm"
include "oveq2.mm"
include "biantrurd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "bitr3d.mm"
include "rspcev.mm"
include "sylan.mm"
include "oveq1.mm"
include "seqeq1.mm"
include "fveq1d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "spcegv.mm"
include "sylc.mm"
include "ex.mm"
include "impbid.mm"
include "iota5.mm"
include "mpan2.mm"

theorem gsumval2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let vz: setvar z
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume gsumval2.b: |- B = ( Base ` G )
  assume gsumval2.p: |- .+ = ( +g ` G )
  assume gsumval2.g: |- ( ph -> G e. V )
  assume gsumval2.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume gsumval2.f: |- ( ph -> F : ( M ... N ) --> B )
  assume gsumval2a.o: |- O = { x e. B | A. y e. B ( ( x .+ y ) = y /\ ( y .+ x ) = y ) }
  assume gsumval2a.f: |- ( ph -> -. ran F C_ O )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint .+ x
  disjoint .+ y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint G z
  disjoint M m
  disjoint M n
  disjoint M z
  disjoint N m
  disjoint N n
  disjoint N z
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F z
  disjoint O f
  disjoint O m
  disjoint O n
  disjoint O z
  disjoint .+ m
  disjoint .+ n
  disjoint .+ z
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph z
  assert |- ( ph -> ( G gsum F ) = ( seq M ( .+ , F ) ` N ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    #
    cM
    cN
    cfz
    co
    #
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    #
    wceq
    #
    vz
    cv
    #
    @3
    c.pl
    cF
    @2
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @2
    cuz
    cfv
    #
    wrex
    #
    vm
    wex
    #
    vz
    cio
    #
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    wph
    @0
    cF
    crn
    cO
    wss
    #
    cG
    c0g
    cfv
    #
    @1
    cfz
    crn
    wcel
    #
    @14
    c1
    cF
    ccnv
    cvv
    cO
    cdif
    cima
    #
    chash
    cfv
    #
    cfz
    co
    @20
    vf
    cv
    #
    wf1o
    @6
    @21
    c.pl
    cF
    @22
    ccom
    c1
    cseq
    cfv
    wceq
    wa
    vf
    wex
    vz
    cio
    #
    cif
    #
    cif
    #
    @14
    wph
    vz
    vy
    @1
    cB
    c.pl
    vf
    vm
    vn
    cF
    cG
    cO
    cV
    @20
    cvv
    @18
    vx
    gsumval2.b
    @18
    eqid
    gsumval2.p
    gsumval2a.o
    wph
    @20
    eqidd
    gsumval2.g
    wph
    cM
    cN
    cfz
    ovexd
    gsumval2.f
    gsumval
    wph
    @25
    @24
    @14
    wph
    @17
    @18
    @24
    gsumval2a.f
    iffalsed
    wph
    @19
    @14
    @23
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @19
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @26
    gsumval2.n
    cM
    cN
    eluzel2
    syl
    #
    wph
    @29
    @27
    gsumval2.n
    cM
    cN
    eluzelz
    syl
    cfz
    cz
    cz
    cxp
    #
    wfn
    #
    @26
    @27
    @19
    @31
    cz
    cpw
    #
    cfz
    wf
    @32
    fzf
    @31
    @33
    cfz
    ffn
    ax-mp
    cz
    cz
    cM
    cN
    cfz
    fnovrn
    mp3an1
    syl2anc
    iftrued
    eqtrd
    eqtrd
    wph
    @16
    cvv
    wcel
    #
    @14
    @16
    wceq
    cN
    @15
    fvex
    wph
    @13
    vz
    @16
    cvv
    wph
    @13
    @6
    @16
    wceq
    #
    wb
    @34
    wph
    @13
    @35
    wph
    @12
    @35
    vm
    wph
    @10
    @35
    vn
    @11
    wph
    @5
    @9
    @35
    wph
    @5
    cM
    @2
    wceq
    #
    cN
    @3
    wceq
    #
    wa
    #
    @9
    @35
    wi
    wph
    @29
    @5
    @38
    wb
    gsumval2.n
    @2
    @3
    cM
    cN
    fzopth
    syl
    @38
    @35
    @9
    @8
    @16
    wceq
    @38
    @16
    @8
    @38
    cN
    @3
    @15
    @7
    @38
    cM
    @2
    c.pl
    cF
    @36
    @37
    simpl
    seqeq1d
    @36
    @37
    simpr
    fveq12d
    eqcomd
    @6
    @8
    @16
    eqeq1
    syl5ibrcom
    syl6bi
    impd
    rexlimdvw
    exlimdv
    wph
    @35
    @13
    wph
    @35
    wa
    @26
    @1
    cM
    @3
    cfz
    co
    #
    wceq
    #
    @6
    @3
    @15
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @28
    wrex
    #
    @13
    wph
    @26
    @35
    @30
    adantr
    wph
    @29
    @35
    @44
    gsumval2.n
    @43
    @35
    vn
    cN
    @28
    @3
    cN
    wceq
    #
    @42
    @43
    @35
    @45
    @40
    @42
    @45
    @39
    @1
    @3
    cN
    cM
    cfz
    oveq2
    eqcomd
    biantrurd
    @45
    @41
    @16
    @6
    @3
    cN
    @15
    fveq2
    eqeq2d
    bitr3d
    rspcev
    sylan
    @12
    @44
    vm
    cM
    cz
    @2
    cM
    wceq
    #
    @10
    @43
    vn
    @11
    @28
    @2
    cM
    cuz
    fveq2
    @46
    @5
    @40
    @9
    @42
    @46
    @4
    @39
    @1
    @2
    cM
    @3
    cfz
    oveq1
    eqeq2d
    @46
    @8
    @41
    @6
    @46
    @3
    @7
    @15
    c.pl
    cF
    @2
    cM
    seqeq1
    fveq1d
    eqeq2d
    anbi12d
    rexeqbidv
    spcegv
    sylc
    ex
    impbid
    adantr
    iota5
    mpan2
    eqtrd
end
