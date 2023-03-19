include "wa.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "srgbinomlem3.mm"
include "srgbinomlem4.mm"
include "oveq12d.mm"
include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wceq.mm"
include "csrg.mm"
include "srgmgp.mm"
include "syl.mm"
include "srgmnd.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "3jca.mm"
include "adantr.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "mulgnn0cl.mm"
include "jca.mm"
include "srgdi.mm"
include "eqtrd.mm"
include "cz.mm"
include "elfzelz.mm"
include "bcpasc.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "bccl.mm"
include "adantl.mm"
include "peano2zm.mm"
include "syl2anc.mm"
include "fznn0sub.mm"
include "elfznn0.mm"
include "srgcl.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "ccmn.mm"
include "srgcmn.mm"
include "fzfid.mm"
include "eqid.mm"
include "gsummptfidmadd.mm"
include "3eqtr4d.mm"

theorem srgbinomlem
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let vj: setvar j
  assume srgbinom.s: |- S = ( Base ` R )
  assume srgbinom.m: |- .X. = ( .r ` R )
  assume srgbinom.t: |- .x. = ( .g ` R )
  assume srgbinom.a: |- .+ = ( +g ` R )
  assume srgbinom.g: |- G = ( mulGrp ` R )
  assume srgbinom.e: |- .^ = ( .g ` G )
  assume srgbinomlem.r: |- ( ph -> R e. SRing )
  assume srgbinomlem.a: |- ( ph -> A e. S )
  assume srgbinomlem.b: |- ( ph -> B e. S )
  assume srgbinomlem.c: |- ( ph -> ( A .X. B ) = ( B .X. A ) )
  assume srgbinomlem.n: |- ( ph -> N e. NN0 )
  assume srgbinomlem.i: |- ( ps -> ( N .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint R k
  disjoint S k
  disjoint .x. k
  disjoint .X. k
  disjoint .^ k
  disjoint k ph
  disjoint .+ k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint N j
  disjoint R j
  disjoint S j
  disjoint .x. j
  disjoint .X. j
  disjoint .^ j
  disjoint j ph
  assert |- ( ( ph /\ ps ) -> ( ( N + 1 ) .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... ( N + 1 ) ) |-> ( ( ( N + 1 ) _C k ) .x. ( ( ( ( N + 1 ) - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  proof
    wph
    wps
    wa
    #
    cN
    cA
    cB
    c.pl
    co
    #
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    @2
    cB
    c.xp
    co
    #
    c.pl
    co
    #
    cR
    vk
    cc0
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    @6
    @8
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @8
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vk
    @7
    cN
    @8
    c1
    cmin
    co
    #
    cbc
    co
    #
    @13
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    #
    @6
    @1
    c.ex
    co
    #
    cR
    vk
    @7
    @6
    @8
    cbc
    co
    #
    @13
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @0
    @3
    @16
    @4
    @21
    c.pl
    wph
    wps
    cA
    cB
    c.pl
    cR
    cS
    c.x
    c.xp
    vk
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem.i
    srgbinomlem3
    wph
    wps
    cA
    cB
    c.pl
    cR
    cS
    c.x
    c.xp
    vk
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem.i
    srgbinomlem4
    oveq12d
    @0
    @23
    @2
    @1
    c.xp
    co
    #
    @5
    @0
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    #
    @1
    cS
    wcel
    #
    w3a
    #
    @23
    @28
    wceq
    wph
    @32
    wps
    wph
    @29
    @30
    @31
    wph
    cR
    csrg
    wcel
    #
    @29
    srgbinomlem.r
    cR
    cG
    srgbinom.g
    srgmgp
    syl
    #
    srgbinomlem.n
    wph
    cR
    cmnd
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @31
    wph
    @33
    @35
    srgbinomlem.r
    cR
    srgmnd
    syl
    #
    srgbinomlem.a
    srgbinomlem.b
    cS
    c.pl
    cR
    cA
    cB
    srgbinom.s
    srgbinom.a
    mndcl
    syl3anc
    #
    3jca
    adantr
    cS
    c.xp
    c.ex
    cG
    cN
    @1
    cS
    cR
    cG
    srgbinom.g
    srgbinom.s
    mgpbas
    #
    srgbinom.e
    cR
    c.xp
    cG
    srgbinom.g
    srgbinom.m
    mgpplusg
    mulgnn0p1
    syl
    @0
    @33
    @2
    cS
    wcel
    #
    @36
    @37
    w3a
    #
    wa
    #
    @28
    @5
    wceq
    wph
    @43
    wps
    wph
    @33
    @42
    srgbinomlem.r
    wph
    @41
    @36
    @37
    wph
    @29
    @30
    @31
    @41
    @34
    srgbinomlem.n
    @39
    cS
    c.ex
    cG
    cN
    @1
    @40
    srgbinom.e
    mulgnn0cl
    syl3anc
    srgbinomlem.a
    srgbinomlem.b
    3jca
    jca
    adantr
    cS
    c.pl
    cR
    c.xp
    @2
    cA
    cB
    srgbinom.s
    srgbinom.a
    srgbinom.m
    srgdi
    syl
    eqtrd
    wph
    @27
    @22
    wceq
    wps
    wph
    @27
    cR
    vk
    @7
    @14
    @19
    c.pl
    co
    #
    cmpt
    #
    cgsu
    co
    @22
    wph
    @26
    @45
    cR
    cgsu
    wph
    vk
    @7
    @25
    @44
    wph
    @8
    @7
    wcel
    #
    wa
    #
    @9
    @18
    caddc
    co
    #
    @13
    c.x
    co
    #
    @25
    @44
    @47
    @48
    @24
    @13
    c.x
    wph
    @30
    @8
    cz
    wcel
    #
    @48
    @24
    wceq
    @46
    srgbinomlem.n
    @8
    cc0
    @6
    elfzelz
    #
    @8
    cN
    bcpasc
    syl2an
    oveq1d
    @47
    @35
    @9
    cn0
    wcel
    #
    @18
    cn0
    wcel
    #
    @13
    cS
    wcel
    #
    @49
    @44
    wceq
    wph
    @35
    @46
    @38
    adantr
    #
    wph
    @30
    @50
    @52
    @46
    srgbinomlem.n
    @51
    @8
    cN
    bccl
    syl2an
    #
    @47
    @30
    @17
    cz
    wcel
    #
    @53
    wph
    @30
    @46
    srgbinomlem.n
    adantr
    @47
    @50
    @57
    @46
    @50
    wph
    @51
    adantl
    @8
    peano2zm
    #
    syl
    @17
    cN
    bccl
    #
    syl2anc
    @47
    @33
    @11
    cS
    wcel
    #
    @12
    cS
    wcel
    #
    @54
    wph
    @33
    @46
    srgbinomlem.r
    adantr
    @47
    @29
    @10
    cn0
    wcel
    #
    @36
    @60
    wph
    @29
    @46
    @34
    adantr
    #
    @46
    @62
    wph
    @8
    cc0
    @6
    fznn0sub
    adantl
    wph
    @36
    @46
    srgbinomlem.a
    adantr
    cS
    c.ex
    cG
    @10
    cA
    @40
    srgbinom.e
    mulgnn0cl
    syl3anc
    @47
    @29
    @8
    cn0
    wcel
    #
    @37
    @61
    @63
    @46
    @64
    wph
    @8
    @6
    elfznn0
    adantl
    wph
    @37
    @46
    srgbinomlem.b
    adantr
    cS
    c.ex
    cG
    @8
    cB
    @40
    srgbinom.e
    mulgnn0cl
    syl3anc
    cS
    cR
    c.xp
    @11
    @12
    srgbinom.s
    srgbinom.m
    srgcl
    syl3anc
    #
    cS
    c.pl
    c.x
    cR
    @9
    @18
    @13
    srgbinom.s
    srgbinom.t
    srgbinom.a
    mulgnn0dir
    syl13anc
    eqtr3d
    mpteq2dva
    oveq2d
    wph
    vk
    @7
    cS
    @14
    @19
    c.pl
    @15
    cR
    @20
    srgbinom.s
    srgbinom.a
    wph
    @33
    cR
    ccmn
    wcel
    srgbinomlem.r
    cR
    srgcmn
    syl
    wph
    cc0
    @6
    fzfid
    @47
    @35
    @52
    @54
    @14
    cS
    wcel
    @55
    @56
    @65
    cS
    c.x
    cR
    @9
    @13
    srgbinom.s
    srgbinom.t
    mulgnn0cl
    syl3anc
    @47
    @35
    @53
    @54
    @19
    cS
    wcel
    @55
    wph
    @30
    @57
    @53
    @46
    srgbinomlem.n
    @46
    @50
    @57
    @51
    @58
    syl
    @59
    syl2an
    @65
    cS
    c.x
    cR
    @18
    @13
    srgbinom.s
    srgbinom.t
    mulgnn0cl
    syl3anc
    @15
    eqid
    @20
    eqid
    gsummptfidmadd
    eqtrd
    adantr
    3eqtr4d
end
