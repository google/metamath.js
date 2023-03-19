include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "caddc.mm"
include "wa.mm"
include "cfz.mm"
include "cin.mm"
include "chash.mm"
include "cdif.mm"
include "nnzd.mm"
include "ballotlemfval.mm"
include "adantr.mm"
include "cc.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "fzfi.mm"
include "inss1.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0cni.mm"
include "a1i.mm"
include "diffi.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "oveq1d.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "fzspl.mm"
include "ineq1d.mm"
include "indir.mm"
include "syl6eq.mm"
include "syl.mm"
include "c0.mm"
include "disjsn.mm"
include "incom.mm"
include "eqeq1i.mm"
include "sylbb1.mm"
include "adantl.mm"
include "uneq2d.mm"
include "un0.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "difeq1d.mm"
include "difundir.mm"
include "disj3.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "cz.mm"
include "uzid.mm"
include "uznfz.mm"
include "3syl.mm"
include "difss.mm"
include "sseli.mm"
include "nsyl.mm"
include "jctil.mm"
include "hashunsng.mm"
include "sylc.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "addsubd.mm"
include "snssi.mm"
include "df-ss.mm"
include "simpr.mm"
include "3eqtrd.mm"
include "difin2.mm"
include "difid.mm"
include "ineq1i.mm"
include "0in.mm"
include "eqtri.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem ballotlemfp1
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotlemfp1.c: |- ( ph -> C e. O )
  assume ballotlemfp1.j: |- ( ph -> J e. NN )

  disjoint J i
  disjoint i ph
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint C i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( ph -> ( ( -. J e. C -> ( ( F ` C ) ` J ) = ( ( ( F ` C ) ` ( J - 1 ) ) - 1 ) ) /\ ( J e. C -> ( ( F ` C ) ` J ) = ( ( ( F ` C ) ` ( J - 1 ) ) + 1 ) ) ) )

  proof
    wph
    cJ
    cC
    wcel
    #
    wn
    #
    cJ
    cC
    cF
    cfv
    #
    cfv
    #
    cJ
    c1
    cmin
    co
    #
    @2
    cfv
    #
    c1
    cmin
    co
    #
    wceq
    #
    wi
    @0
    @3
    @5
    c1
    caddc
    co
    #
    wceq
    #
    wi
    wph
    @1
    @7
    wph
    @1
    wa
    #
    @3
    c1
    cJ
    cfz
    co
    #
    cC
    cin
    #
    chash
    cfv
    #
    @11
    cC
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    @6
    wph
    @3
    @16
    wceq
    #
    @1
    wph
    vx
    cC
    cP
    vi
    cF
    cJ
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotlemfp1.c
    wph
    cJ
    ballotlemfp1.j
    nnzd
    #
    ballotlemfval
    #
    adantr
    @10
    c1
    @4
    cfz
    co
    #
    cC
    cin
    #
    chash
    cfv
    #
    @20
    cC
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    c1
    cmin
    co
    @22
    @24
    c1
    caddc
    co
    #
    cmin
    co
    @6
    @16
    @10
    @22
    @24
    c1
    @22
    cc
    wcel
    #
    @10
    @22
    @21
    cfn
    wcel
    #
    @22
    cn0
    wcel
    @20
    cfn
    wcel
    #
    @21
    @20
    wss
    @28
    c1
    @4
    fzfi
    #
    @20
    cC
    inss1
    #
    @20
    @21
    ssfi
    mp2an
    #
    @21
    hashcl
    ax-mp
    nn0cni
    #
    a1i
    @24
    cc
    wcel
    #
    @10
    @24
    @23
    cfn
    wcel
    #
    @24
    cn0
    wcel
    @29
    @35
    @30
    @20
    cC
    diffi
    ax-mp
    @23
    hashcl
    ax-mp
    nn0cni
    #
    a1i
    @10
    1cnd
    subsub4d
    @10
    @5
    @25
    c1
    cmin
    wph
    @5
    @25
    wceq
    #
    @1
    wph
    vx
    cC
    cP
    vi
    cF
    @4
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotlemfp1.c
    wph
    cJ
    c1
    @18
    wph
    1zzd
    zsubcld
    ballotlemfval
    #
    adantr
    oveq1d
    @10
    @13
    @22
    @15
    @26
    cmin
    @10
    @12
    @21
    chash
    @10
    @12
    @21
    cJ
    csn
    #
    cC
    cin
    #
    cun
    #
    @21
    wph
    @12
    @41
    wceq
    #
    @1
    wph
    cJ
    c1
    cuz
    cfv
    wcel
    #
    @42
    wph
    cJ
    cn
    wcel
    @43
    ballotlemfp1.j
    cJ
    elnnuz
    sylib
    #
    @43
    @12
    @20
    @39
    cun
    #
    cC
    cin
    @41
    @43
    @11
    @45
    cC
    c1
    cJ
    fzspl
    #
    ineq1d
    @20
    @39
    cC
    indir
    syl6eq
    syl
    #
    adantr
    @10
    @41
    @21
    c0
    cun
    @21
    @10
    @40
    c0
    @21
    @1
    @40
    c0
    wceq
    #
    wph
    cC
    @39
    cin
    #
    c0
    wceq
    @1
    @48
    cC
    cJ
    disjsn
    @49
    @40
    c0
    cC
    @39
    incom
    eqeq1i
    sylbb1
    #
    adantl
    uneq2d
    @21
    un0
    syl6eq
    eqtrd
    fveq2d
    @10
    @15
    @23
    @39
    cun
    #
    chash
    cfv
    #
    @26
    @10
    @14
    @51
    chash
    wph
    @1
    @14
    @23
    @39
    cC
    cdif
    #
    cun
    #
    @51
    wph
    @43
    @14
    @54
    wceq
    @44
    @43
    @14
    @45
    cC
    cdif
    @54
    @43
    @11
    @45
    cC
    @46
    difeq1d
    @20
    @39
    cC
    difundir
    syl6eq
    syl
    #
    @1
    @53
    @39
    @23
    @1
    @39
    @53
    @1
    @48
    @39
    @53
    wceq
    @50
    @39
    cC
    disj3
    sylib
    eqcomd
    uneq2d
    sylan9eq
    fveq2d
    @10
    cJ
    cz
    wcel
    #
    @35
    cJ
    @23
    wcel
    #
    wn
    #
    wa
    @52
    @26
    wceq
    wph
    @56
    @1
    @18
    adantr
    @10
    @58
    @35
    @10
    cJ
    @20
    wcel
    #
    @57
    wph
    @59
    wn
    #
    @1
    wph
    @56
    cJ
    cJ
    cuz
    cfv
    wcel
    #
    @60
    @18
    cJ
    uzid
    #
    cJ
    c1
    cJ
    uznfz
    #
    3syl
    adantr
    @23
    @20
    cJ
    @20
    cC
    difss
    #
    sseli
    nsyl
    @29
    @23
    @20
    wss
    @35
    @30
    @64
    @20
    @23
    ssfi
    mp2an
    jctil
    @23
    cJ
    cz
    hashunsng
    sylc
    eqtrd
    oveq12d
    3eqtr4rd
    eqtrd
    ex
    wph
    @0
    @9
    wph
    @0
    wa
    #
    @3
    @16
    @8
    wph
    @17
    @0
    @19
    adantr
    @65
    @22
    c1
    caddc
    co
    #
    @24
    cmin
    co
    @25
    c1
    caddc
    co
    @16
    @8
    @65
    @22
    c1
    @24
    @27
    @65
    @33
    a1i
    @65
    1cnd
    @34
    @65
    @36
    a1i
    addsubd
    @65
    @13
    @66
    @15
    @24
    cmin
    @65
    @13
    @41
    chash
    cfv
    #
    @21
    @39
    cun
    #
    chash
    cfv
    #
    @66
    wph
    @13
    @67
    wceq
    @0
    wph
    @12
    @41
    chash
    @47
    fveq2d
    adantr
    @0
    @67
    @69
    wceq
    wph
    @0
    @41
    @68
    chash
    @0
    @40
    @39
    @21
    @0
    @39
    cC
    wss
    #
    @40
    @39
    wceq
    cJ
    cC
    snssi
    #
    @39
    cC
    df-ss
    sylib
    uneq2d
    fveq2d
    adantl
    @65
    @0
    @28
    cJ
    @21
    wcel
    #
    wn
    #
    wa
    @69
    @66
    wceq
    wph
    @0
    simpr
    @65
    @73
    @28
    @65
    @59
    @72
    @65
    @56
    @61
    @60
    wph
    @56
    @0
    @18
    adantr
    @62
    @63
    3syl
    @21
    @20
    cJ
    @31
    sseli
    nsyl
    @32
    jctil
    @21
    cJ
    cC
    hashunsng
    sylc
    3eqtrd
    @65
    @15
    @54
    chash
    cfv
    #
    @23
    c0
    cun
    #
    chash
    cfv
    #
    @24
    wph
    @15
    @74
    wceq
    @0
    wph
    @14
    @54
    chash
    @55
    fveq2d
    adantr
    @0
    @74
    @76
    wceq
    wph
    @0
    @54
    @75
    chash
    @0
    @53
    c0
    @23
    @0
    @70
    @53
    c0
    wceq
    @71
    @70
    @53
    cC
    cC
    cdif
    #
    @39
    cin
    #
    c0
    @39
    cC
    cC
    difin2
    @78
    c0
    @39
    cin
    c0
    @77
    c0
    @39
    cC
    difid
    ineq1i
    @39
    0in
    eqtri
    syl6eq
    syl
    uneq2d
    fveq2d
    adantl
    @65
    @75
    @23
    chash
    @75
    @23
    wceq
    @65
    @23
    un0
    a1i
    fveq2d
    3eqtrd
    oveq12d
    @65
    @5
    @25
    c1
    caddc
    wph
    @37
    @0
    @38
    adantr
    oveq1d
    3eqtr4d
    eqtrd
    ex
    jca
end
