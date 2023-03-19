include "cn0.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cur.mm"
include "cfv.mm"
include "mgpbas.mm"
include "eqid.mm"
include "ringidval.mm"
include "mulg0.mm"
include "syl.mm"
include "csrg.mm"
include "srgridm.mm"
include "syl2anc.mm"
include "srglidm.mm"
include "3eqtr4rd.mm"
include "eqtrd.mm"
include "wa.mm"
include "cmnd.mm"
include "srgmgp.mm"
include "adantr.mm"
include "simpr.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "mulgnn0cl.mm"
include "srgass.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem srgpcomp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.xp: class .X.
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume srgpcomp.s: |- S = ( Base ` R )
  assume srgpcomp.m: |- .X. = ( .r ` R )
  assume srgpcomp.g: |- G = ( mulGrp ` R )
  assume srgpcomp.e: |- .^ = ( .g ` G )
  assume srgpcomp.r: |- ( ph -> R e. SRing )
  assume srgpcomp.a: |- ( ph -> A e. S )
  assume srgpcomp.b: |- ( ph -> B e. S )
  assume srgpcomp.k: |- ( ph -> K e. NN0 )
  assume srgpcomp.c: |- ( ph -> ( A .X. B ) = ( B .X. A ) )


  assert |- ( ph -> ( ( K .^ B ) .X. A ) = ( A .X. ( K .^ B ) ) )

  proof
    cK
    cn0
    wcel
    wph
    cK
    cB
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    cA
    @0
    c.xp
    co
    #
    wceq
    #
    srgpcomp.k
    wph
    vx
    cv
    #
    cB
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    cA
    @5
    c.xp
    co
    #
    wceq
    #
    wi
    wph
    cc0
    cB
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    cA
    @9
    c.xp
    co
    #
    wceq
    #
    wi
    wph
    vy
    cv
    #
    cB
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    cA
    @14
    c.xp
    co
    #
    wceq
    #
    wi
    wph
    @13
    c1
    caddc
    co
    #
    cB
    c.ex
    co
    #
    cA
    c.xp
    co
    #
    cA
    @19
    c.xp
    co
    #
    wceq
    #
    wi
    wph
    @3
    wi
    vx
    vy
    cK
    @4
    cc0
    wceq
    #
    @8
    @12
    wph
    @23
    @6
    @10
    @7
    @11
    @23
    @5
    @9
    cA
    c.xp
    @4
    cc0
    cB
    c.ex
    oveq1
    #
    oveq1d
    @23
    @5
    @9
    cA
    c.xp
    @24
    oveq2d
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @8
    @17
    wph
    @25
    @6
    @15
    @7
    @16
    @25
    @5
    @14
    cA
    c.xp
    @4
    @13
    cB
    c.ex
    oveq1
    #
    oveq1d
    @25
    @5
    @14
    cA
    c.xp
    @26
    oveq2d
    eqeq12d
    imbi2d
    @4
    @18
    wceq
    #
    @8
    @22
    wph
    @27
    @6
    @20
    @7
    @21
    @27
    @5
    @19
    cA
    c.xp
    @4
    @18
    cB
    c.ex
    oveq1
    #
    oveq1d
    @27
    @5
    @19
    cA
    c.xp
    @28
    oveq2d
    eqeq12d
    imbi2d
    @4
    cK
    wceq
    #
    @8
    @3
    wph
    @29
    @6
    @1
    @7
    @2
    @29
    @5
    @0
    cA
    c.xp
    @4
    cK
    cB
    c.ex
    oveq1
    #
    oveq1d
    @29
    @5
    @0
    cA
    c.xp
    @30
    oveq2d
    eqeq12d
    imbi2d
    wph
    @10
    cR
    cur
    cfv
    #
    cA
    c.xp
    co
    #
    @11
    wph
    @9
    @31
    cA
    c.xp
    wph
    cB
    cS
    wcel
    #
    @9
    @31
    wceq
    srgpcomp.b
    cS
    c.ex
    cG
    cB
    @31
    cS
    cR
    cG
    srgpcomp.g
    srgpcomp.s
    mgpbas
    #
    cR
    @31
    cG
    srgpcomp.g
    @31
    eqid
    #
    ringidval
    srgpcomp.e
    mulg0
    syl
    #
    oveq1d
    wph
    cA
    @31
    c.xp
    co
    #
    cA
    @11
    @32
    wph
    cR
    csrg
    wcel
    #
    cA
    cS
    wcel
    #
    @37
    cA
    wceq
    srgpcomp.r
    srgpcomp.a
    cS
    cR
    c.xp
    @31
    cA
    srgpcomp.s
    srgpcomp.m
    @35
    srgridm
    syl2anc
    wph
    @9
    @31
    cA
    c.xp
    @36
    oveq2d
    wph
    @38
    @39
    @32
    cA
    wceq
    srgpcomp.r
    srgpcomp.a
    cS
    cR
    c.xp
    @31
    cA
    srgpcomp.s
    srgpcomp.m
    @35
    srglidm
    syl2anc
    3eqtr4rd
    eqtrd
    @13
    cn0
    wcel
    #
    wph
    @17
    @22
    wph
    @40
    @17
    @22
    wi
    wph
    @40
    wa
    #
    @17
    @22
    @41
    @17
    wa
    @20
    @15
    cB
    c.xp
    co
    #
    @21
    @41
    @20
    @42
    wceq
    @17
    @41
    @20
    @14
    cB
    c.xp
    co
    #
    cA
    c.xp
    co
    #
    @42
    @41
    @19
    @43
    cA
    c.xp
    @41
    cG
    cmnd
    wcel
    #
    @40
    @33
    @19
    @43
    wceq
    wph
    @45
    @40
    wph
    @38
    @45
    srgpcomp.r
    cR
    cG
    srgpcomp.g
    srgmgp
    syl
    adantr
    #
    wph
    @40
    simpr
    #
    wph
    @33
    @40
    srgpcomp.b
    adantr
    #
    cS
    c.xp
    c.ex
    cG
    @13
    cB
    @34
    srgpcomp.e
    cR
    c.xp
    cG
    srgpcomp.g
    srgpcomp.m
    mgpplusg
    mulgnn0p1
    syl3anc
    #
    oveq1d
    @41
    @14
    cB
    cA
    c.xp
    co
    #
    c.xp
    co
    #
    @14
    cA
    cB
    c.xp
    co
    #
    c.xp
    co
    #
    @44
    @42
    @41
    @50
    @52
    @14
    c.xp
    wph
    @50
    @52
    wceq
    @40
    wph
    @52
    @50
    srgpcomp.c
    eqcomd
    adantr
    oveq2d
    @41
    @38
    @14
    cS
    wcel
    #
    @33
    @39
    @44
    @51
    wceq
    wph
    @38
    @40
    srgpcomp.r
    adantr
    #
    @41
    @45
    @40
    @33
    @54
    @46
    @47
    @48
    cS
    c.ex
    cG
    @13
    cB
    @34
    srgpcomp.e
    mulgnn0cl
    syl3anc
    #
    @48
    wph
    @39
    @40
    srgpcomp.a
    adantr
    #
    cS
    cR
    c.xp
    @14
    cB
    cA
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    @41
    @38
    @54
    @39
    @33
    @42
    @53
    wceq
    @55
    @56
    @57
    @48
    cS
    cR
    c.xp
    @14
    cA
    cB
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    3eqtr4d
    eqtrd
    adantr
    @17
    @41
    @42
    @16
    cB
    c.xp
    co
    #
    @21
    @15
    @16
    cB
    c.xp
    oveq1
    @41
    @58
    cA
    @43
    c.xp
    co
    #
    @21
    @41
    @38
    @39
    @54
    @33
    @58
    @59
    wceq
    @55
    @57
    @56
    @48
    cS
    cR
    c.xp
    cA
    @14
    cB
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    @41
    @43
    @19
    cA
    c.xp
    @41
    @19
    @43
    @49
    eqcomd
    oveq2d
    eqtrd
    sylan9eqr
    eqtrd
    ex
    expcom
    a2d
    nn0ind
    mpcom
end
